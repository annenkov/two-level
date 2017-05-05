build :
	linja

clean :
	rm *.clean *.olean *.d *.ilean
	rm ./types/*.clean ./types/*.olean ./types/*.d ./types/*.ilean

default : build
