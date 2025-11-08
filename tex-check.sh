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
    warn=$(biber --tool --validate-datamodel --nolog --outfile /dev/null "$f" 2>&1)

    # Filter out harmless patterns
    warn_filtered=$(echo "$warn" | grep "WARN" \
      | grep -v "invalid in data model - ignoring" \
      | grep -v "Invalid field '[a-z]*' for entrytype '[a-z]*'")

    if [ -n "$warn_filtered" ]; then
      status="BIBER WARN"
      echo "--- biber warnings in $f ---"
      echo "$warn_filtered"
      echo "--------------------------------"
    fi
  fi

  printf "%-50s  %s\n" "$f" "$status"
done

