#!/bin/sh

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
NC='\033[0m'

main()
{
	make testLanceWilliamsHAC || exit

	if [ $# -eq 1 ]
	then
		if [ ! -f "graphs/$1.in" ]
		then
			echo "error: graphs/$1.in does not exist"
			exit 1
		fi
		run_test "$1"
	elif [ $# -eq 0 ]
	then
		for i in $(seq 4)
		do
			run_test "$i"
		done
	else
		echo "usage: $0 [test number]"
		exit 1
	fi
}

run_test()
{
	i="$1"
	out="LanceWilliamsHACTests/$i.out"
	exp="LanceWilliamsHACTests/$i.exp"

	rm -f "$out"
	./testLanceWilliamsHAC "graphs/$i.in" | sort -n > "$out"

	if [ ! -f "$exp" ]
	then
		echo -e "=========== ${YELLOW}[$i] No Expected Output Available${NC} ==========="
		return
	fi
	
	if diff "$out" "$exp" > /dev/null
	then
		echo -e "=========== ${GREEN}[$i] Output Matches${NC} ==========="
	else
		echo -e "=========== ${RED}[$i] Output Mismatch${NC} ==========="
		echo -e "${RED}Your output:${NC}"
		cat "$out"
		echo -e "${RED}Expected output:${NC}"
		cat "$exp"
		echo -e "${RED}Your output in: $out${NC}"
		echo -e "${RED}Expected output in: $exp${NC}"
	fi
}

main "$@"

