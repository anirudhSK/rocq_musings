## first.p4 file
We run the operation `hdr.h.b = hdr.h.a;`
## second.p4 file
We run the operation `hdr.h.b = 1;`
## test-a
In this test we only include `hdr.h.a` in the `headers_to_check` definition `Definition headers_to_check : list Header := [first_generated.h_a; second_generated.h_a].` as a result we get an `unsat` since the headers we checked were never actually modified.
## test-b
In this test we switched from the `a` header to the `b` header in the `headers_to_check` variable and got a `sat` as expected. The result is the same if we include all four headers.