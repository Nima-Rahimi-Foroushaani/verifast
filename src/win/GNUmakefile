win/Perf.cmxa: win/caml_perf.c win/Perf.mli win/Perf.ml win/Stopwatch.mli win/caml_stopwatch.c win/caml_seterrormode.c win/SetErrorMode.ml
	cd win; ocamlopt.opt -c -opaque Stopwatch.mli Stopwatch.ml
	cd win; ocamlopt.opt -a -o Perf.cmxa caml_perf.c Perf.mli Perf.ml caml_stopwatch.c Stopwatch.cmx caml_seterrormode.c SetErrorMode.ml

clean::
	rm -f win/*.o win/*.a win/*.cm*
