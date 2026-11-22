#!/bin/sh
# Generate crypto_core.h and crypto_core_salsa20.h in the current directory, as
# NaCl 20110221's `do` script does for the crypto_core/salsa20/ref implementation.
# The commands below are those of `do`, with its loop variables fixed. They read
# api.h, MACROS, PROTOTYPES.c and PROTOTYPES.cpp from the current directory.
set -eu
o=crypto_core
p=salsa20
op=${o}_${p}
implementationdir=crypto_core/salsa20/ref
opi=`echo "$implementationdir" | tr ./- ___`
	  (
	    echo "#ifndef ${o}_H"
	    echo "#define ${o}_H"
	    echo ""
	    echo "#include \"${op}.h\""
	    echo ""
	    egrep "${o}"'$|'"${o}"'\(|'"${o}"'_' < MACROS \
	    | sed "s/$o/$op/" | while read mop
	    do
	      echo "#define ${mop} ${mop}" | sed "s/$op/$o/"
	    done
	    echo "#define ${o}_PRIMITIVE \"${p}\""
	    echo "#define ${o}_IMPLEMENTATION ${op}_IMPLEMENTATION"
	    echo "#define ${o}_VERSION ${op}_VERSION"
	    echo ""
	    echo "#endif"
	  ) > "$o.h"
	  (
	    echo "#ifndef ${op}_H"
	    echo "#define ${op}_H"
	    echo ""
	    sed 's/[ 	]CRYPTO_/ '"${opi}"'_/g' < api.h
	    echo '#ifdef __cplusplus'
	    echo '#include <string>'
	    egrep "${o}"'$|'"${o}"'\(|'"${o}"'_' < PROTOTYPES.cpp \
	    | sed "s/$o/$opi/"
	    echo 'extern "C" {'
	    echo '#endif'
	    egrep "${o}"'$|'"${o}"'\(|'"${o}"'_' < PROTOTYPES.c \
	    | sed "s/$o/$opi/"
	    echo '#ifdef __cplusplus'
	    echo '}'
	    echo '#endif'
	    echo ""
	    egrep "${o}"'$|'"${o}"'\(|'"${o}"'_' < MACROS \
	    | sed "s/$o/$opi/" | while read mopi
	    do
	      echo "#define ${mopi} ${mopi}" | sed "s/$opi/$op/"
	    done
	    echo "#define ${op}_IMPLEMENTATION \"${implementationdir}\""
	    echo "#ifndef ${opi}_VERSION"
	    echo "#define ${opi}_VERSION \"-\""
	    echo "#endif"
	    echo "#define ${op}_VERSION ${opi}_VERSION"
	    echo ""
	    echo "#endif"
	  ) > "$op.h"
