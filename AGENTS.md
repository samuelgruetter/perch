### Leave theorem statements unchanged

If a theorem statement was not written by you, DO NOT change it.
Only exception: If a theorem statement contains an obvious mistake, fix the mistake.

### Before committing

After you have run `git add` with the files you want to add, read the output of `git diff --staged --stat`. For each file that has both additions and deletions (i.e. both + signs and - signs on its stat line), read the output of `git diff --staged -- path/to/the/file.ext` and decide if the diff is as minimal as it can be.
Remove all superflous changes that are not related to the given task, and do `git add` and the diff minimality check again.
If you edited files at this stage, re-build and re-run the tests as needed and make sure they still pass.

### Commit message format

Only git commit if the task was given in a separate prompt markdown file and you still remember where that file is.
When committing, do not try to infer the commit format by looking at previous commits. Instead, always use the following commit message format:

1) One line summarizing the change, without mentioning the prompt file path, but actually summarizing the prompt file and your reaction to it on one line
2) An empty line as per git conventions
3) A line with heading '## Prompt'
4) An empty line
5) Include the markdown prompt file vebatim
6) Two empty lines
7) A line with the heading '## Outcome'
8) A summary of what you thought and did
9) Co-authored-by trailer, where you credit yourself with your model name and version.

Make sure that no lines in your commit message are wider than 72 chars,
except for the prompt file, just include that verbatim.

Adapt the following bash command in order to commit:

```
{
  cat <<'EOF'
(put parts 1 to 4 here)
EOF

  cat path/to/the/prompt_file.md

  cat <<'EOF'
(put parts 6 to 9 here)
EOF
} | git commit -F -
```
