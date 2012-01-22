all : ui.png clamp.png clampBefore.png clampAfter.png trim.png trimBefore.png trimAfter.png backwards.png

.SECONDARY :

%.exe : %.hs
	ghc --make $< -o $@

%.png : ui.exe
	./ui.exe -w 200 -h 200 -o $@ --selection=$*

clean :
	rm -f *.exe *.o *.hi *.pdf *.png *~ *.errors

exp : all
	scp *.png byorgey@eniac.seas.upenn.edu:public_html/hosted/