# Preface

*A peer view, offered only as a motto. Two readers may ask different questions of one whole. If they meet the same question, one bit must answer both. The sentence is not a theorem. The theorems are named below.*

This note is offered as a mathematical text. It is not a claim about physics, about mind, or about the history of an idea.

The object is a finite controlled tree. At each nonterminal history a deterministic adaptive policy chooses an action, and a prescribed kernel returns an outcome. An exact causal seed is one random variable, drawn once, together with one deterministic decoder. The same seed and the same decoder must reproduce the prescribed transcript law for every policy. In particular, two policies that share a history and take the same action receive the same answer on each atom of the seed. Their later questions may still lead them down different branches.

The finite causal Shannon theorem bounds the least Shannon entropy \(C(T)\) of such a seed. Let \(X_\pi\) be the terminal transcript under a policy \(\pi\), and let \(I_\pi=-\log_2 P_\pi(X_\pi)\). Write

\[
F^\ast(t)=\min_\pi\Pr(I_\pi\le t),
\qquad
L(T)=\int_0^\infty\bigl(1-F^\ast(t)\bigr)\,dt.
\]

There is a finite seed \(S_G\) with

\[
L(T)\le C(T)\le H(S_G)\le L(T)+\frac{1+\log_2 e}{2}.
\]

The additive constant is about \(1.221\) bits and has a prior coupling-theoretic provenance. What is distinctive in the present statement is the single decoder, required to agree at every shared history. The quantity bounded is the entropy of the seed. It is not the storage of the decoder, and it is not the decoder's running time. The upper bound is a causal greedy construction. It does not follow from coupling the terminal laws alone.

Three small results fix how that statement should be read.

**The clock.** An information clock on probabilities in \((0,1]\) that never runs backward, is unchanged when a passage is cut in two, and counts one outcome of a fair toss as one bit, is uniquely \(d(p)=-\log_2 p\). Along a finite history the reading is the sum of the steps. A certain step contributes nothing. The order of the steps is assumed. The reading is not physical time. Formalization: `CausalSeed/LetItBe.lean`.

**The two friends.** On the smallest tree in which two friends share one fair question and then take different private actions, each of deterministic output zero, one has \(L(T)=C(T)=1\). Giving both friends the same bit is an exact causal seed of entropy \(1\). Assigning them opposite bits matches each transcript law and is not the run of any shared decoder. Equal marginals are not a causal coupling. The obstruction is agreement at the shared history, not a cheaper pairing. Formalization: `CausalSeed/ManyFriends.lean`.

**The two grooves.** The same distinction can be stated before any tree is drawn. One record stores a single fair bit and plays it in both grooves; its entropy is \(1\), and the grooves agree on every atom. The other stores two independent fair bits; its entropy is \(2\), and the grooves agree with probability \(1/2\). Under either record, each groove alone is a fair bit. Any finite seed whose answer on one groove is a deterministic function of the seed, and is fair, has entropy at least \(1\). The shared record attains the bound. Thus the law of each groove does not determine the entropy of the whole, and unfolding a prepared whole is not, by itself, an entropy bound. Formalization: `CausalSeed/FrozenLight.lean`.

One further realization is recorded because it is easy to mistake for the theorem. A finite tree carries a kernel at every history and every action. Drawing those cells independently produces one finite table. Reading the cell of the history actually reached is a deterministic decoder, and it does not depend on which playback is running. For every playback, the law of the transcript is the prescribed product along the path taken. Two playbacks that meet at the same history and choose the same action read the same cell. This shows that one whole can serve every allowed playback. It does not show that the table is the cheapest seed. Formalization: `CausalSeed/OneWhole.lean`.

A metaphor is sometimes useful, and it is easy to overread. A record prepared before the needle drops is an image of a seed together with a decoder: the rule of response is fixed, and a history appears only when a groove is chosen. David Bohm's account of an implicate order — a drop of dye that disappears under shear and reappears when the motion is reversed — has the same shape. He himself warned that the experiment, like a hologram, catches only part of the idea, because the order is inserted beforehand.

The comparison stops where the theorem starts. Bohm's image does not determine \(L(T)\). The finite causal Shannon theorem is not a reinterpretation of that image, and it is not evidence for it. The two grooves are the separation: the same appearances, two entropies. No statement about electrons, worldlines, tachyons, or the number of particles follows from the information theorem. The historical picture of many crossings of a single worldline, recalled from Feynman's Nobel lecture, is an image of the word *one*. It is not a premise.

Free will is not identified with the entropy of the seed. If a choice is the placing of the needle, it is made after the record is fixed, and it contributes no bit. If a choice is the draw of the seed, it is a single draw, made before any question is asked. Those are different arrows. Neither is a theorem about a human will.

The general sandwich is the greedy theorem in `CausalSeed/Entropy.lean`. It is not rederived in these notes. The proofs cited above are formalized in Lean 4 with no `sorry`, on the three standard axioms of the kernel. What a reader must still trust are the definitions: the tree, the policy, the decoder, and the identification of \(C(T)\) and \(L(T)\) with those definitions.

What remains outside the mathematics is a question an experiment can refuse. Replaying one history does not identify the record. Two listeners who may play different grooves can already, inside the model, tell a shared toss from a product of independent tosses. That is a distinction of joint laws. It is not a trace in a detector, and it is not offered as one.

I ask only that the quantifiers be read before the image.

Jan Mikulík  
10 November 2026
