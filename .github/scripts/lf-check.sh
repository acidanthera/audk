#!/bin/bash

lint_line_endings()
{
  # All the files that should be excluded in either check, followed by all the files that are meant to be LF.
  cmd="find . -not -type d \\
  -not \( -path \"./.git/*\" -o -path \"./OpenCorePkg/*\" -o -path \"*/Bin/*\" \\
    -o -name \"*.bin\" -o -name \"*.bmp\" -o -name \"*.cer\" -o -name \"*.pem\" -o -name \"*.png\" -o -name \"*.pyd\" \\
    -o -name \"X11IncludeHack\" \\
  \) \\
  $([[ $1 = "LF" ]] && echo '-not ' || echo '')\( \( -path \"./BaseTools/BinWrappers/PosixLike/*\" -not -name \"*.*\" \) \\
    -o -name \".gitmodules\" -o -name \"*.sh\" -o -name \"*.ps\" \\
    -o -name \"*.pbx*\" -o -path \"./EmulatorPkg/Unix/*init\" -o -name \"BuildEnv\" \\
    -o -name \"diff.order\" -o -name \"TestArgv.log\" \\
  \) \\
  -exec perl -0777 -lne 'if($([[ $1 = "LF" ]] && echo '/(?<!\r)\n/' || echo '/\r\n/')) {print \"$([[ $1 = "LF" ]] && echo 'Bare ' || echo 'CR')LF in {}\n\";}' '{}' \";\""

  echo $(eval "$cmd")
}

a="$(lint_line_endings 'LF')"
b="$(lint_line_endings 'CRLF')"

sym="$([[ $a != "" ]] && echo -e "${a}\n$b" || echo "$b")"

if [ "${sym}" != "" ]; then
  echo "*** AUDK contains the following line ending errors: ***"
  echo "$sym"
  exit 1
fi
