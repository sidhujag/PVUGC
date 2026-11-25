# Public tables and selective wire labels

The **group labels** in the Praxis proof are public handles for encoded group elements. The **wire-state labels** in the signer are independent 32-byte bearer secrets. The encrypted gate rows can be published at deposit. Someone with a complete authorized set of wire-state labels can assemble and broadcast the same signed Pay. Bitcoin needs only the signatures. Where two authorized descriptors differ on a wire, publishing both authorized views can disclose both labels for that particular wire. The [two-view signing argument](GUARDED_NONCE.md#sharing-the-digest-labels-across-phases) accounts for this union.

The unresolved claim is that the public factor table delivers only labels in those views. The claim must count all signs, group comparisons, native search results, source-proof encodings, scratch toggles and corrupt setup participants' information. A party obtaining a further qualifying source witness can use the public package again.

## An averaged bound for authorized searches

Write $g$ for the number of possible values of each ordinary search coefficient. Allow an observer to read the coordinates supporting its authorized witnesses. This also gives it every scalar search sum on those supports. Each choice of coordinate can depend on the already observed values, independent public information and the centered constant $r_0$. It cannot depend on an unaccounted pairing result involving unread coefficients.

For a comparison $Wr=y$ chosen from this transcript, suppose its restriction to the **union of all unread coordinates** has rank at least $s$. The probability of this rank event and a hit is at most $g^{-s}$ under the independent native sampler. Under the paper's centered sampler it is at most

$$
\bigl(1+\lceil s(g-1)/2\rceil/g\bigr)g^{-s}.
$$

Choose $s$ independent unread pivot columns and read every remaining nonpivot. Conditional on $r_0$, the unread ordinary coordinates are exchangeable. A reveal order that selects indices before seeing their values and places the pivots last preserves the joint law of the ordered values and $r_0$. Fix the independent observer coins. For each fixed $r_0$ and ordered nonpivot values, the reveal path is determined and a hit specifies at most one pivot tuple. That tuple and $r_0$ specify at most one centering draw. For a fixed nonpivot sum there are at most $g+\lceil s(g-1)/2\rceil$ compatible values of $r_0$. Each pivot tuple and centering draw have joint unconditioned weight $g^{-(s+1)}$ in the ordered experiment. Summing the joint masses gives the bound. It is averaged over setup, not conditional on an arbitrary observed $r_0$. Rank four can come from several closed labels, even when the targeted label uses only three coefficients.

## Counting earlier informative comparisons

There is a separate bound for an **affine equality decision tree** on a fixed closed triple. Give away all other coefficients, fix independent table coins and let $H$ count all scalar affine equality tests on the triple. Give the observer $J$ guesses of the exact tuple. Until the first successful tuple guess, its answers to unsuccessful guesses disclose only failure. With independent uniform entries its success probability is at most

$$
\min\!\left(1,\frac{J(1+H+\binom H2)+\binom H3}{g^3}\right).
$$

Fix the observer's coins and follow the execution in which tuple guesses are answered as misses. Record the positions of comparisons that hold and reduce the affine solution space left by earlier true comparisons. Those positions determine the entire equality transcript. Equalities already implied are forced and every other test outside the recorded positions fails. There can be at most three dimension reductions. A transcript with zero, one or two reductions can name at most $J$ successful tuples. A transcript with three reductions leaves at most one tuple. Counting position sets proves the result, including adaptive choices made *after* an informative equality. For the centered sampler one may bound the numerator before capping by the extra factor $1+\lceil3(g-1)/2\rceil/g$, by the same count over the possible $r_0$ values.

This lemma is relevant because the native left factors omit the search coefficients, the right factors are affine in them, and a type-III pairing keeps the exponent affine after other coins are fixed. It is a bound for that equality interface. It does not account by itself for bytes of real curve encodings, other side information or the distribution of a malicious arming transcript. $H$ includes initial aliases and comparisons against earlier handles as well as search comparisons. Once $H$ is on the order of $g$ the bound offers little or no protection. It does not separate the cost of an honest opening from the adversary's budget at the authors' parameters. [Native sampler and factors](frontend/fullkem/encrypt.go) · [Praxis Appendix B](https://arxiv.org/pdf/2611.28552#page=51)

## Remaining case for the proposed table

Praxis Lemma B.6 classifies a usable stack of **total** row rank at most three without a hash-kernel vector. A nonzero target column then requires a constituent witness selecting that target. A globally high-rank stack can have low rank on the unread coordinates. Projecting that stack can destroy the Frobenius tie identities. A short projected vector need not lift to the globally short Module-SIS vector required by the paper. Neither counting bound above supplies that missing structural result. It remains necessary to classify or quantitatively bound target-bearing comparisons after all permitted disclosures.

The pinned native table uses eight possibilities per coefficient, so a triple has just **512 possible wrapping inputs**. The two-Pay encrypted-row prototype uses an ideal source of eligible labels. Independent Bitcoin signing roles can preserve a proven honest role's guarantee when the committee goes offline. They cannot prove selective release for the honest role's actual table. [Pinned selectors](frontend/fullrows/pinned_scratch.go) · [Two-Pay row test](frontend/guardednonce/shared_subtree_test.go)
