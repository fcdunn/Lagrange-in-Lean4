-- Import relevant parts of Mathlib
import Mathlib.Tactic
import Mathlib.Util.Delaborators

set_option warningAsError false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

-- We restrict to the case of finite groups for simplicity only.
-- Lagrange's Theorem holds in greater generality, of course.
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (x y : G)
variable (H : Subgroup G) [Fintype H]



-- We define the left coset as the image under the multiplication map of x with H.
def lcoset : Finset G := ((x * ·) '' H).toFinset

-- Define (left) index of H in G
def lcosetSet : Finset (Finset G) := { s : Finset G | ∃ g : G, s = lcoset g H }

def lindex : ℕ := Finset.card (lcosetSet H)




-- Show that the cosets cover G
lemma coset_cover : (lcosetSet H).biUnion id = Finset.univ := by
  apply Finset.Subset.antisymm
  -- Of course, any memeber of the union of cosets is an element of the group
  · simp only [Finset.subset_univ]
  -- Now, we show that any x ∈ G also lies in xH.
  · intro x hx
    simp only [Finset.mem_biUnion, id_eq]
    use lcoset x H
    constructor
    · dsimp[lcosetSet]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      use x
    simp only [lcoset, Set.mem_toFinset]
    use 1
    constructor
    · exact H.one_mem
    · simp only [mul_one]



-- Prove cosets are pairwise disjoint

lemma lcoset_pdisj : (lcosetSet H : Set (Finset G)).PairwiseDisjoint id := by
  intro s hs t ht
  contrapose
  dsimp only [Function.onFun, id]
  intro h_disj
  rw[Finset.not_disjoint_iff_nonempty_inter] at h_disj
  -- First, we show that if the intersection is nonempty then we have a containment.
  -- We do this for general elements u,v in order to show equality by applying to x,y and y,x.
  have h_incl (u v : G) (hd : (lcoset u H ∩ lcoset v H).Nonempty) : lcoset u H ⊆ lcoset v H := by
  -- Take an element w in the intersection
    rcases hd with ⟨w, hw⟩
    simp only [Finset.mem_inter, lcoset, Set.mem_toFinset] at hw
    obtain ⟨h1, h1H, huw⟩ := hw.1
    obtain ⟨h2, h2H, hvw⟩ := hw.2
    simp only at huw hvw
    -- Rewrite these slightly for what we're about to do.
    apply_fun (· * h1⁻¹) at huw
    simp only [mul_inv_cancel_right] at huw
    apply_fun (· * h2⁻¹) at hvw
    simp only [mul_inv_cancel_right] at hvw
    have huv : v⁻¹ * u ∈ H := by
      rw[huw,hvw]
      rw[mul_inv_rev, inv_inv, mul_inv_mul_mul_cancel]
      exact H.mul_mem h2H (H.inv_mem h1H)
    -- We now show the inclusion element-wise.
    intro a ha
    simp only [lcoset, Set.mem_toFinset] at ha
    obtain ⟨h3, h3H, hua⟩ := ha
    simp only at hua
    -- From our previous work, we know which element of H to use.
    simp only [lcoset, Set.mem_toFinset]
    use v⁻¹ * u * h3
    simp only
    constructor
    · exact H.mul_mem huv h3H
    · rw[mul_assoc, hua, mul_inv_cancel_left]
  -- Now we have shown the one-way inclusion, we simply apply it twice to give equality.
  simp only [SetLike.mem_coe,lcosetSet,Finset.mem_filter, Finset.mem_univ, true_and] at hs
  obtain ⟨ x, hx ⟩ := hs
  simp only [SetLike.mem_coe,lcosetSet,Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨ y, hy ⟩ := ht
  rw[hx,hy]
  rw[hx,hy] at h_disj
  apply Finset.Subset.antisymm
  · exact h_incl x y h_disj
  · rw[Finset.inter_comm] at h_disj
    exact h_incl y x h_disj









lemma size_G_eq_sum_cosets : Fintype.card G = ∑ s ∈ lcosetSet H, s.card := by
  change (Finset.univ : Finset G).card = ∑ s ∈ lcosetSet H, s.card
  -- Apply our coset_cover lemma
  have h_lemma :  ((lcosetSet H).biUnion id).card = (Finset.univ : Finset G).card  :=
    congr_arg Finset.card (coset_cover H)
  rw[← h_lemma]
  -- To show this equality, we just need to simplify and use our disjointness lemma
  rw[Finset.card_biUnion]
  · simp only [id_eq]
  apply lcoset_pdisj


-- Prove cosets of H are all isomorphic (as sets)
def coset_iso : H ≃ lcoset x H where
  -- Isomorphism is of course given by left-multiplication by x
  toFun h := by
    use x * h
    simp only [lcoset, Set.mem_toFinset]
    use h
    simp
  -- Inverse given by left multiplication by x^-1.
  invFun y := by
    use x⁻¹ * y
    have hy := y.property
    simp only [lcoset, Set.mem_toFinset] at hy
    rcases hy with ⟨h, hH, xhy⟩
    rw[← xhy]
    rw[inv_mul_cancel_left]
    exact hH
  left_inv h := by
    simp only [inv_mul_cancel_left]
  right_inv y := by
    simp only [mul_inv_cancel_left]

-- Use this to show that all cosets are of the same size (the size of H)
lemma coset_size : ∀ s ∈ lcosetSet H, s.card = Fintype.card H := by
  intro s hs
  rw[lcosetSet] at hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  obtain ⟨ x, hx⟩ := hs
  rw[hx]
  rw[Fintype.card_congr (coset_iso x H)]
  simp only [Fintype.card_coe]

-- Now, we prove the ``index'' version of Lagrange's theorem using the above lemmas.

theorem LG_index : (Fintype.card G) = (lindex H) * (Fintype.card H) := by
  have h_size :  Fintype.card G = ∑ s ∈ lcosetSet H, s.card  :=
    size_G_eq_sum_cosets H
  rw[h_size]
  have h_sum : ∑ s ∈ lcosetSet H, s.card = ∑ s ∈ lcosetSet H, Fintype.card H := by
    apply Finset.sum_congr rfl
    exact coset_size H
  rw[h_sum]
  rw[Finset.sum_const]
  rfl



-- Prove subgroup divisibility version of Lagrange's theorem

theorem LG_subgroup : Fintype.card H ∣ Fintype.card G := by
  use lindex H
  rw[mul_comm]
  have index_thm : (Fintype.card G) = (lindex H) * (Fintype.card H) :=
    LG_index H
  exact index_thm


-- Prove element order divisibility version of Lagrange's theorem
-- (via subgroup generated by element)
-- We use the inbuilt orderOf x for the order of an element,
-- Subgroup.zpowers x for the subgroup it generates,
-- and the lemma Nat.card_zpowers.

theorem LG_element : orderOf x ∣ Fintype.card G := by
  let H := Subgroup.zpowers x
  have h_order : orderOf x = Fintype.card H := by
    rw[←  Nat.card_eq_fintype_card]
    rw[Nat.card_zpowers]
  have h_subgroup : Fintype.card H ∣ Fintype.card G :=
    LG_subgroup H
  rw[h_order]
  exact h_subgroup
