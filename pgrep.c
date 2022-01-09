/*
 * pgrep/pkill -- utilities to filter the process table
 *
 * Copyright 2000 Kjetil Torgrim Homme <kjetilho@ifi.uio.no>
 * Changes by Albert Cahalan, 2002,2006.
 * Changes by Roberto Polli <rpolli@babel.it>, 2012.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <unistd.h>
#include <ctype.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <signal.h>
#include <pwd.h>
#include <grp.h>
#include <regex.h>
#include <errno.h>
#include <getopt.h>
#include <stdbool.h>
#include <time.h>

#if defined(ENABLE_PWAIT) && !defined(HAVE_PIDFD_OPEN)
#include <sys/epoll.h>
#include <sys/syscall.h>
#endif

/* EXIT_SUCCESS is 0 */
/* EXIT_FAILURE is 1 */
#define EXIT_USAGE 2
#define EXIT_FATAL 3
#define XALLOC_EXIT_CODE EXIT_FATAL

#include "c.h"
#include "fileutils.h"
#include "nsutils.h"
#include "nls.h"
#include "xalloc.h"
#include "proc/readproc.h"
#include "proc/sig.h"
#include "proc/devname.h"
#include "proc/sysinfo.h"

#define grow_size(x) do { \
	if ((x) < 0 || (size_t)(x) >= INT_MAX / 5 / sizeof(struct el)) \
		xerrx(EXIT_FAILURE, _("integer overflow")); \
	(x) = (x) * 5 / 4 + 4; \
} while (0)

static enum {
    PGREP = 0,
    PKILL,
#ifdef ENABLE_PWAIT
    PWAIT,
#endif
} prog_mode;

struct el {
	long	num;
	char *	str;
};

/* User supplied arguments */

static int opt_full = 0;
static int opt_long = 0;
static int opt_longlong = 0;
static int opt_oldest = 0;
static int opt_older = 0;
static int opt_newest = 0;
static int opt_negate = 0;
static int opt_exact = 0;
static int opt_count = 0;
static int opt_signal = SIGTERM;
static int opt_lock = 0;
static int opt_case = 0;
static int opt_echo = 0;
static int opt_threads = 0;
static pid_t opt_ns_pid = 0;
static bool use_sigqueue = false;
static union sigval sigval = {0};

static const char *opt_delim = "\n";
static struct el *opt_pgrp = NULL;
static struct el *opt_rgid = NULL;
static struct el *opt_pid = NULL;
static struct el *opt_ppid = NULL;
static struct el *opt_sid = NULL;
static struct el *opt_term = NULL;
static struct el *opt_euid = NULL;
static struct el *opt_ruid = NULL;
static struct el *opt_nslist = NULL;
static char *opt_pattern = NULL;
static char *opt_pidfile = NULL;
static char *opt_runstates = NULL;

/* by default, all namespaces will be checked */
static int ns_flags = 0x3f;

static struct el *split_list (const char *restrict str, int (*convert)(const char *, struct el *))
{
	char *copy;
	char *ptr;
	char *sep_pos;
	int i = 0;
	int size = 0;
	struct el *list = NULL;

	if (str[0] == '\0')
		return NULL;

	copy = xstrdup (str);
	ptr = copy;

	do {
		if (i == size) {
			grow_size(size);
			/* add 1 because slot zero is a count */
			list = xrealloc (list, (1 + size) * sizeof *list);
		}
		sep_pos = strchr (ptr, ',');
		if (sep_pos)
			*sep_pos = 0;
		/* Use ++i instead of i++ because slot zero is a count */
		if (list && !convert (ptr, &list[++i]))
			exit (EXIT_USAGE);
		if (sep_pos)
			ptr = sep_pos + 1;
	} while (sep_pos);

	free (copy);
	if (!i) {
		free (list);
		list = NULL;
	} else {
		list[0].num = i;
	}
	return list;
}

/* strict_atol returns a Boolean: TRUE if the input string
 * contains a plain number, FALSE if there are any non-digits. */
static int strict_atol (const char *restrict str, long *restrict value)
{
	long res = 0;
	long sign = 1;

	if (*str == '+')
		++str;
	else if (*str == '-') {
		++str;
		sign = -1;
	}

	for ( ; *str; ++str) {
		if (! isdigit (*str))
			return (0);
		res *= 10;
		res += *str - '0';
	}
	*value = sign * res;
	return 1;
}

#include <sys/file.h>

/* We try a read lock. The daemon should have a write lock.
 * Seen using flock: FreeBSD code */
static int has_flock(int fd)
{
	return flock(fd, LOCK_SH|LOCK_NB)==-1 && errno==EWOULDBLOCK;
}

/* We try a read lock. The daemon should have a write lock.
 * Seen using fcntl: libslack */
static int has_fcntl(int fd)
{
	struct flock f;  /* seriously, struct flock is for a fnctl lock! */
	f.l_type = F_RDLCK;
	f.l_whence = SEEK_SET;
	f.l_start = 0;
	f.l_len = 0;
	return fcntl(fd,F_SETLK,&f)==-1 && (errno==EACCES || errno==EAGAIN);
}

static struct el *read_pidfile(void)
{
	char buf[12];
	int fd;
	struct stat sbuf;
	char *endp;
	int n, pid;
	struct el *list = NULL;

	fd = open(opt_pidfile, O_RDONLY|O_NOCTTY|O_NONBLOCK);
	if(fd<0)
		goto just_ret;
	if(fstat(fd,&sbuf) || !S_ISREG(sbuf.st_mode) || sbuf.st_size<1)
		goto out;
	/* type of lock, if any, is not standardized on Linux */
	if(opt_lock && !has_flock(fd) && !has_fcntl(fd))
		goto out;
	memset(buf,'\0',sizeof buf);
	n = read(fd,buf,sizeof buf-1);
	if (n<1)
		goto out;
	pid = strtoul(buf,&endp,10);
	if(endp<=buf || pid<1 || pid>0x7fffffff)
		goto out;
	if(*endp && !isspace(*endp))
		goto out;
	list = xmalloc(2 * sizeof *list);
	list[0].num = 1;
	list[1].num = pid;
out:
	close(fd);
just_ret:
	return list;
}

static int conv_uid (const char *restrict name, struct el *restrict e)
{
	struct passwd *pwd;

	if (strict_atol (name, &e->num))
		return (1);

	pwd = getpwnam (name);
	if (pwd == NULL) {
		xwarnx(_("invalid user name: %s"), name);
		return 0;
	}
	e->num = (int) pwd->pw_uid;
	return 1;
}


static int conv_gid (const char *restrict name, struct el *restrict e)
{
	struct group *grp;

	if (strict_atol (name, &e->num))
		return 1;

	grp = getgrnam (name);
	if (grp == NULL) {
		xwarnx(_("invalid group name: %s"), name);
		return 0;
	}
	e->num = (int) grp->gr_gid;
	return 1;
}


static int conv_pgrp (const char *restrict name, struct el *restrict e)
{
	if (! strict_atol (name, &e->num)) {
		xwarnx(_("invalid process group: %s"), name);
		return 0;
	}
	if (e->num == 0)
		e->num = getpgrp ();
	return 1;
}


static int conv_sid (const char *restrict name, struct el *restrict e)
{
	if (! strict_atol (name, &e->num)) {
		xwarnx(_("invalid session id: %s"), name);
		return 0;
	}
	if (e->num == 0)
		e->num = getsid (0);
	return 1;
}


static int conv_num (const char *restrict name, struct el *restrict e)
{
	if (! strict_atol (name, &e->num)) {
		xwarnx(_("not a number: %s"), name);
		return 0;
	}
	return 1;
}


static int conv_str (const char *restrict name, struct el *restrict e)
{
	e->str = xstrdup (name);
	return 1;
}


static int conv_ns (const char *restrict name, struct el *restrict e)
{
	int rc = conv_str(name, e);
	int id;

	ns_flags = 0;
	id = get_ns_id(name);
	if (id == -1)
		return 0;
	ns_flags |= (1 << id);

	return rc;
}

static int match_numlist (long value, const struct el *restrict list)
{
	int found = 0;
	if (list != NULL) {
		int i;
		for (i = list[0].num; i > 0; i--) {
			if (list[i].num == value) {
				found = 1;
				break;
			}
		}
	}
	return found;
}

static int match_strlist (const char *restrict value, const struct el *restrict list)
{
	int found = 0;
	if (list != NULL) {
		int i;
		for (i = list[0].num; i > 0; i--) {
			if (! strcmp (list[i].str, value)) {
				found = 1;
				break;
			}
		}
	}
	return found;
}

static int match_ns (const proc_t *task, const proc_t *ns_task)
{
	int found = 1;
	int i;
	for (i = 0; i < NUM_NS; i++) {
		if (ns_flags & (1 << i)) {
			if (task->ns[i] != ns_task->ns[i]) {
				found = 0;
				break;
			}
		}
	}
	return found;
}

static void output_numlist (const struct el *restrict list, int num)
{
	int i;
	const char *delim = opt_delim;
	for (i = 0; i < num; i++) {
		if(i+1==num)
			delim = "\n";
		printf ("%ld%s", list[i].num, delim);
	}
}

static void output_strlist (const struct el *restrict list, int num)
{
/* FIXME: escape codes */
	int i;
	const char *delim = opt_delim;
	for (i = 0; i < num; i++) {
		if(i+1==num)
			delim = "\n";
		printf ("%lu %s%s", list[i].num, list[i].str, delim);
	}
}

static PROCTAB *do_openproc (void)
{
	PROCTAB *ptp;
	int flags = 0;

	if (opt_pattern || opt_full || opt_longlong)
		flags |= PROC_FILLCOM;
	if (opt_ruid || opt_rgid)
		flags |= PROC_FILLSTATUS;
	if (opt_oldest || opt_newest || opt_pgrp || opt_sid || opt_term || opt_older)
		flags |= PROC_FILLSTAT;
	if (!(flags & PROC_FILLSTAT))
		flags |= PROC_FILLSTATUS;  /* FIXME: need one, and PROC_FILLANY broken */
	if (opt_ns_pid)
		flags |= PROC_FILLNS;
	if (opt_euid && !opt_negate) {
		int num = opt_euid[0].num;
		int i = num;
		uid_t *uids = xmalloc (num * sizeof (uid_t));
		while (i-- > 0) {
			uids[i] = opt_euid[i+1].num;
		}
		flags |= PROC_UID;
		ptp = openproc (flags, uids, num);
	} else {
		ptp = openproc (flags);
	}
	return ptp;
}

static regex_t * do_regcomp (void)
{
	regex_t *preg = NULL;

	if (opt_pattern) {
		char *re;
		char errbuf[256];
		int re_err;

		preg = xmalloc (sizeof (regex_t));
		if (opt_exact) {
			re = xmalloc (strlen (opt_pattern) + 5);
			sprintf (re, "^(%s)$", opt_pattern);
		} else {
			re = opt_pattern;
		}

		re_err = regcomp (preg, re, REG_EXTENDED | REG_NOSUB | opt_case);

		if (opt_exact) free(re);

		if (re_err) {
			regerror (re_err, preg, errbuf, sizeof(errbuf));
			fputs(errbuf,stderr);
			exit (EXIT_USAGE);
		}
	}
	return preg;
}

/*
 * SC_ARG_MAX used to return the maximum size a command line can be
 * however changes to the kernel mean this can be bigger than we can
 * alloc. Clamp it to 128kB like xargs and friends do
 * Should also not be smaller than POSIX_ARG_MAX which is 4096
 */
static size_t get_arg_max(void)
{
#define MIN_ARG_SIZE 4096u
#define MAX_ARG_SIZE (128u * 1024u)

    size_t val = sysconf(_SC_ARG_MAX);

    if (val < MIN_ARG_SIZE)
	val = MIN_ARG_SIZE;
    if (val > MAX_ARG_SIZE)
	val = MAX_ARG_SIZE;

    return val;
}
static struct el * select_procs (int *num)
{
	PROCTAB *ptp;
	proc_t task;
	proc_t subtask;
	unsigned long long saved_start_time;      /* for new/old support */
	pid_t saved_pid = 0;                      /* for new/old support */
	int matches = 0;
	int size = 0;
	regex_t *preg;
	pid_t myself = getpid();
	struct el *list = NULL;
        long cmdlen = get_arg_max() * sizeof(char);
	char *cmdline = xmalloc(cmdlen);
	char *cmdsearch = xmalloc(cmdlen);
	char *cmdoutput = xmalloc(cmdlen);
	proc_t ns_task;
	time_t now;
	int uptime_secs;


	ptp = do_openproc();
	preg = do_regcomp();

	now = time(NULL);
	if ((uptime_secs=uptime(0,0)) == 0)
		xerrx(EXIT_FAILURE, "uptime");

	if (opt_newest) saved_start_time =  0ULL;
	else saved_start_time = ~0ULL;

	if (opt_newest) saved_pid = 0;

	memset(&task, 0, sizeof (task));
	memset(&subtask, 0, sizeof (subtask));
	while(readproc(ptp, &task)) {
		int match = 1;

		if (task.XXXID == myself)
			continue;
		else if (opt_newest && task.start_time < saved_start_time)
			match = 0;

		if (task.cmdline && (opt_longlong || opt_full) ) {
			int i = 0;
			long bytes = cmdlen;
			char *str = cmdline;

			/* make sure it is always NUL-terminated */
			*str = '\0';

			while (task.cmdline[i] && bytes > 1) {
				const int len = snprintf(str, bytes, "%s%s", i ? " " : "", task.cmdline[i]);
				if (len < 0) {
					*str = '\0';
					break;
				}
				if (len >= bytes) {
					break;
				}
				str += len;
				bytes -= len;
				i++;
			}
		}

		if (match && opt_pattern) {
			strncpy (cmdoutput, task.cmd, cmdlen - 1);
			cmdoutput[cmdlen - 1] = '\0';
			strncpy (cmdsearch, task.cmd, cmdlen - 1);
			cmdsearch[cmdlen - 1] = '\0';

			if (regexec (preg, cmdsearch, 0, NULL, 0) != 0)
				match = 0;
		}

		if (match ^ opt_negate) {	/* Exclusive OR is neat */
			if (opt_newest) {
				if (saved_start_time == task.start_time &&
				    saved_pid > task.XXXID)
					continue;
				saved_start_time = task.start_time;
				saved_pid = task.XXXID;
				matches = 0;
			}
			if (opt_oldest) {
				if (saved_start_time == task.start_time &&
				    saved_pid < task.XXXID)
					continue;
				saved_start_time = task.start_time;
				saved_pid = task.XXXID;
				matches = 0;
			}
			if (matches == size) {
				grow_size(size);
				list = xrealloc(list, size * sizeof *list);
			}
			if (list && (opt_long || opt_longlong || opt_echo)) {
				list[matches].num = task.XXXID;
				list[matches++].str = xstrdup (cmdoutput);
			} else if (list) {
				list[matches++].num = task.XXXID;
			} else {
				xerrx(EXIT_FAILURE, _("internal error"));
			}
		}
	}
	closeproc (ptp);
	*num = matches;

        free(cmdline);
        free(cmdsearch);
        free(cmdoutput);

	if (preg) {
		regfree(preg);
		free(preg);
	}

	return list;
}

static void parse_opts (int argc, char **argv)
{
	char opts[64] = "";
	int opt;
	int criteria_count = 0;

	enum {
		SIGNAL_OPTION = CHAR_MAX + 1,
		NS_OPTION,
		NSLIST_OPTION,
	};
	static const struct option longopts[] = {
		{"newest", no_argument, NULL, 'n'},
		{NULL, 0, NULL, 0}
	};

    prog_mode = PGREP;
	strcat (opts, "lad:vw");

	strcat (opts, "LF:cfinoxP:O:g:s:u:U:G:t:r:?Vh");

	while ((opt = getopt_long (argc, argv, opts, longopts, NULL)) != -1) {
		switch (opt) {
		case 'n':   /* Solaris: match only the newest */
			if (opt_oldest|opt_negate|opt_newest)
				usage ('?');
			opt_newest = 1;
			++criteria_count;
			break;
		}
	}

	if (argc - optind == 1)
		opt_pattern = argv[optind];
	else if (argc - optind > 1)
		xerrx(EXIT_USAGE, _("only one pattern can be provided\n"
				     "Try `%s --help' for more information."),
				     program_invocation_short_name);
	else if (criteria_count == 0)
		xerrx(EXIT_USAGE, _("no matching criteria specified\n"
				     "Try `%s --help' for more information."),
				     program_invocation_short_name);
}

int main (int argc, char **argv)
{
	struct el *procs;
	int num;
	int i;
	int kill_count = 0;

	setlocale (LC_ALL, "");
	bindtextdomain(PACKAGE, LOCALEDIR);
	textdomain(PACKAGE);
	atexit(close_stdout);

	parse_opts (argc, argv);

	procs = select_procs (&num);
	
	output_numlist (procs,num);
	return !num;
    /* Not sure if it is possible to get here */
    return -1;
}
