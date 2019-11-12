DEVDIR = ./theories

build :
	linja

clean :
	rm $(DEVDIR)/*.clean $(DEVDIR)/*.olean $(DEVDIR)/*.d $(DEVDIR)/*.ilean
	rm $(DEVDIR)/types/*.clean $(DEVDIR)/types/*.olean $(DEVDIR)/types/*.d $(DEVDIR)/types/*.ilean

default : build
