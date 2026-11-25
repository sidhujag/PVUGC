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

## An exact rank test after two openings

Take one symmetric base-field stack $W=(W_c)_c$ from a generic comparison. Let $J$ embed a chosen subset of unread coordinates in the full coordinate space. To preserve the entire unread part of that comparison, choose the entire unread set. To search for a witness selecting one target coordinate $j$, one may instead take $J=e_j$. Write

$$
F_c=W_cJ,\quad T=\sum_c\operatorname{im}F_c,\quad S=\sum_c\operatorname{im}F_c^\top,\quad
h=\dim T,\quad s=\dim S,\quad d=\dim(J^\top T).
$$

Here $s$ is the rank of the vertically stacked search equations restricted to the chosen coordinates. The value $h$ counts independent **full column vectors** that different cells attach to them. These can be different even for a single scratch bit.

**Symmetric completion theorem.** Among all families of symmetric matrices $M_c$ with $M_c J=F_c$, the least possible simultaneous total row rank is exactly

$$
h+s-d.
$$

For the lower bound let $L$ be the common space spanned by their columns. Then $T\subseteq L$ and $S\subseteq J^\top L$ by symmetry. Also $J^\top T\subseteq S$ because $J^\top F_c$ is symmetric. Enlarging $T$ enough to cover $S$ under projection costs at least $s-d$ dimensions.

For attainment extend $T$ by lifts of a complement of $J^\top T$ in $S$. The resulting $L$ has dimension $h+s-d$ and $J^\top L=S$. Let $B$ be a basis matrix of $L$, write $F_c=B A_c$, and set $G=J^\top B$. The rows of $A_c$ lie in $S$, so $A_c$ vanishes on $\ker G^\top$. The rule $G^\top x\mapsto A_c x$ is well-defined and defines a symmetric pairing on $\operatorname{im}G^\top$, since $G A_c=J^\top F_c$ is symmetric. Complete it to a symmetric matrix $C_c$ with $C_cG^\top=A_c$ by choosing a basis extending that subspace and filling the unconstrained symmetric block. Then $M_c=B C_c B^\top$ realizes the bound. This argument uses finite-field linear algebra and allows arbitrary changes to the complementary square block in each cell.

**Certificate for the actual source relation.** Suppose the target column is nonzero. For a candidate $L$ of dimension at most three, impose $BC_cB^\top J=F_c$, symmetry of $C_c$, every Booleanity and source-constraint test, and the original Frobenius ties across all cells. These are linear equations over the base field, expanding extension coefficients in the paper's basis. If feasible and the public hash $z$ is injective on $L$, Lemma B.6 decomposes the completed stack into honest witness stacks of the original source. At least one witness selects the target. Otherwise every honest summand would have zero target column. To find it with $L$ in hand, fix the homogeneous coordinate to one and enumerate at most four binary choices of the remaining pivot coordinates, checking the full Boolean system and target bit on each assignment. This is a static certificate given an explicit comparison stack. Recovering or simulating such stacks in a full adaptive generic-group transcript is a further requirement. [Praxis Lemmas B.4–B.6](https://arxiv.org/pdf/2611.28552#page=52)

When $h=3$ and $d=s$, the only candidate space of dimension at most three is $T$ itself. One linear solve exactly decides whether a passing, tied completion of that rank exists. Lower values of $h$ can permit several candidate spaces, and a failed solve for one space does not exclude the others. A value $h+s-d>3$ rules out this completion method even before imposing the source constraints. It does not identify an unauthorized signature or an expression that an attacker can realize. When $J$ consists of just the target, a successful certificate can still supply its witness even if matching **all** unread columns is impossible. Such a completion need not reproduce the original pairing comparison.

For a single nonzero target column, $s=1$. The minimum is $h$ if any cell has a nonzero target diagonal, and $h+1$ otherwise. In particular four independent cell columns already force total rank at least four, although the unread restriction to this bit has rank one. There is a further source-specific exclusion when every target diagonal vanishes. In Step 3 of Lemma B.6 take the linear matrix test $M\mapsto M_{jj}$, which vanishes on every matching cell. Each constituent witness with nonzero weight would have $w_j^2=0$, contradicting the preserved nonzero column. Thus no usable hash-injective rank-three-or-less completion exists in that case. This excludes a proof route for such stacks without asserting they occur in a real Pay transcript.

**What the actual ties already enforce on one target.** For $J=e_j$, assume $1\le h\le3$ and $z$ is injective on $T$. Let the base-field columns of $B$ span $T$. For the paper's three extension-field slices indexed by $a$, set $p_a=B^\top z_a$ and write $W_a e_j=B v_a$. By Lemma B.5 the $p_a$ span the extension-field coordinate space of dimension $h$. Multiplying the original ties $W_a z_b=W_b z_a$ on the left by $e_j^\top$ gives $v_a^\top p_b=v_b^\top p_a$. Consequently every linear dependence among the $p_a$ is also a dependence among the $v_a$, as one can test against the spanning $p_b$. There is a unique symmetric extension-field matrix $D$ with $v_a=D p_a$. Thus $W_a e_j=B D B^\top z_a$ even when the full stack has arbitrarily high rank. This is a bilinear description of one target column. It does not force the other coordinates of a candidate assignment to satisfy the original Pay verifier. The completion test above supplies that missing condition when it succeeds.

## Why per-cell offsets cannot independently mask a selectable scratch bit

Consider a redesign that assigns each cell its own search vector $r_c$ while requiring every legal witness $w$ to have the same scalar search sum $w^\top r_c$ in all cells. The common sum may change from the current scheme. For a scratch bit $j$ that can ever be enabled, the native toggle interface supplies legal witnesses $w$ and $w+e_j$ with identical receipt and descriptor. Apply the common-sum condition to both and subtract. For every two cells $c,c'$ this gives

$$
e_j^\top(r_c-r_{c'})=0.
$$

Consequently any offsets that preserve that interface must agree on the very coefficient that wraps the label. This identity holds for correlated or independently sampled offsets and applies to any selector implemented with the same free single-bit toggle. Offsets on other source coordinates could affect particular comparisons. Independent entropy **on the target coefficient across cells** requires changing the decoder or the witness encoding. [Actual scratch constraint](frontend/fullrows/pinned_scratch.go) · [Native opening procedure](SHARED_PAY.md#what-goes-in-the-archive)

Two different private Pays may disclose many independent search equations. Both can even disclose both states of an individual wire. The required property is confinement to the union of authorized views, including every legal encoding and toggle, plus the two-view signer's inability to assemble a third signature from that union. The rank certificate covers particular comparisons. A security bound for comparisons outside it, with all earlier disclosures, is still needed for the honest signing role before relying on an offline N-of-N reserve.
