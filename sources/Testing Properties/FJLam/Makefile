default: run

run:
	ghc -o run -fhpc -fforce-recomp Tests --make -main-is "Tests" 

coverage:
	./run
	hpc markup run --exclude=Tests --exclude=FJParser --exclude=FJGenerator

clean: 
	rm -f *.o *dyn* *.hi run run.tix *.html V1/*.o V1/*dyn* V1/*.hi V2/*.o V2/*dyn* V2/*.hi
