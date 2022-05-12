#!/bin/sh

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

main()
{
	make testCentralityMeasures || exit

	if [ $# -eq 2 ]
	then
		if [ ! -f "graphs/$1.in" ]
		then
			echo "error: graphs/$1.in does not exist"
			exit 1
		fi
		if [ "$2" != "c" -a "$2" != "b" -a "$2" != "bn" ]
		then
			echo "error: invalid centrality type '$2'"
			exit 1
		fi
		run_test "$1" "$2"
	elif [ $# -eq 1 ]
	then
		if [ ! -f "graphs/$1.in" ]
		then
			echo "error: graphs/$1.in does not exist"
			exit 1
		fi
		run_test "$1" c
		run_test "$1" b
		run_test "$1" bn
	elif [ $# -eq 0 ]
	then
		for f in graphs/*.in
		do
			i=$(basename "$f" .in)
			for t in c b bn
			do			
				run_test "$i" "$t"
			done
		done
	else
		echo "usage: $0 [test number [c|b|bn]] "
		exit 1
	fi
}

run_test()
{
	i="$1"
	t="$2"
	out="CentralityMeasuresTests/$i$t.out"
	exp="CentralityMeasuresTests/$i$t.exp"

	rm -f "$out"
	./testCentralityMeasures "graphs/$i.in" "$t" > "$out"

	if [ ! -f "$exp" ]
	then
		echo -e "=========== ${YELLOW}[$i$t] No Expected Output Available${NC} ==========="
		return
	fi

	if diff "$out" "$exp" > /dev/null
	then
		echo -e "=========== ${GREEN}[$i$t] Output Matches${NC} ==========="
	else
		echo -e "=========== ${RED}[$i$t] Output Mismatch${NC} ==========="
		echo -e "${RED}Your output:${NC}"
		cat "$out"
		echo -e "${RED}Expected output:${NC}"
		cat "$exp"
		echo -e "${RED}Your output in: $out${NC}"
		echo -e "${RED}Expected output in: $exp${NC}"
	fi
}

main "$@"

