#!/usr/bin/env bash
# Check all .tex and .bib files (plus any extra arguments) for UTF-8 validity and BOMs.

shopt -s nullglob

# collect default + user files
files=( "$@" )

printf "%-50s  %s\n" "FILE" "STATUS"
printf "%-50s  %s\n" "----" "------"

for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  status="OK"

  # check for UTF-8 BOM (EF BB BF)
  if head -c3 "$f" | xxd -p | grep -qi '^efbbbf'; then
    status="BOM FOUND"
  else
    # check encoding validity with iconv
    if ! iconv -f utf-8 -t utf-8 "$f" -o /dev/null 2>/dev/null; then
      status="INVALID UTF-8"
    fi
  fi

  # --- Biber validation (.bib only) ---
  if [[ "$f" == *.bib ]]; then
    tmp_log=$(mktemp)

    biber --tool --validate-datamodel --nolog --outfile /dev/null "$f" >"$tmp_log"

    # show errors unfiltered
    errs=$(grep -E '(^ERROR\b| ERROR - )' "$tmp_log")
    if [ -n "$errs" ]; then
      status="BIBER ERROR"
      echo "--- biber errors in $f ---" >&2
      echo "$errs" >&2
      # fall through to also show warnings if you want
    fi

    # show warnings, but ignore your chosen patterns
    warn_filtered=$(
      grep -E '(^WARN\b| WARN - )' "$tmp_log" \
      | grep -Ev 'invalid in data model - ignoring|Invalid field '\''.*'\'' for entrytype '\''.*'\'''
    )
    if [ -n "$warn_filtered" ] && [ "$status" = "OK" ]; then
      status="BIBER WARN"
      echo "--- biber warnings in $f ---"
      echo "$warn_filtered"
      echo "--------------------------------"
    fi

    rm -f "$tmp_log"
  fi

  printf "%-50s  %s\n" "$f" "$status"
done

