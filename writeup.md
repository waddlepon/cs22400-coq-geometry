# Coq Project Writeup (Tyler Poon)
For this project I tried to formalize Hilbert's axioms in Coq and prove some basic results with them.
I was able to formalize the axioms with the exception of the Axiom of Archimedes(which I didn't formalize because it seemed like I wouldn't need it) and the Axiom of Completeness(which seemed too difficult to formalize/use since it's a second-order axiom), although the correctness of many of my axioms haven't been tested. I also assumed the excluded middle, because geometrical proofs often rely on some of its properties being decidable.

I was able to formalize some proofs following some of the proof sketches in the ohiolink.edu source below, with most of my effort being put towards formalizing plane separation, that any line on a plane divides all points on that plane not on the line into two different sides. Although the construction of the proof is relatively simple, it was a lot of work to formalize, since a lot of arguments relied on forms of contradiction that can be annoying to prove within Coq, or steps that are simple in a geometrical proof but very verbose in Coq. You may also notice that I admit the final bullet point in the pasch_one_intersection(ie that a line through a side of a triangle cannot intersect with both other line segments) proof, since I couldn't figure out how to translate that part of the proof to my axioms in Coq.

If I had more time, I would've seen if I could finish the proof I was doing with side-angle-side congruence, but the congruent angle part of the proof was becoming a bit too much of a mess. Maybe with smarter formalizations of the axioms or a better idea for how to prove it in Coq I could figure it out.

Overall, this was an interesting project although to be honest I think the biggest takeaway for me is that geometrical proofs in Coq are very difficult, which was what I expected. That did force me to spend a lot of time thinking about and looking for fitting theorems to prove, since a lot of classically easy proofs are much more difficult with these axioms or with the specificity of Coq. I do think that if I wanted to expand on the project, it would almost certainly require writing a lot of smart tactics to make these proofs more efficient and concise. I haven't investigated Tarski's axioms at all, but I also feel like there are axiomatizations of geometry that would be easier to work with than Hilbert's especially when reduing to only planar geoemtry.

## Sources
https://en.wikipedia.org/wiki/Hilbert%27s_axioms

https://math.berkeley.edu/~wodzicki/160/Hilbert.pdf

https://etd.ohiolink.edu/acprod/odb_etd/ws/send_file/send?accession=osu1354311965&disposition=inline