import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Dual.Lemmas
import PoincareConjecture.Proofs.Horizon.Topology.Connected.FiniteComplement

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

theorem exists_equiv_of_transverse_functionals
    {a b : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ}
    (ha : a ≠ 0) {v : EuclideanSpace ℝ (Fin 2)}
    (hav : a v = 0) (hbv : b v ≠ 0) :
    ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
      ∀ z, L z = (a z, b z) := by
  have hex : ∃ w, a w ≠ 0 := by
    by_contra! h
    exact ha (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hex
  let A := a.prod b
  have hsurj : Function.Surjective A := by
    rintro ⟨x, y⟩
    refine ⟨(x / a w) • w + ((y - (x / a w) * b w) / b v) • v, ?_⟩
    apply Prod.ext
    · change a _ = x
      simp only [map_add, map_smul, smul_eq_mul, hav, mul_zero, add_zero]
      exact div_mul_cancel₀ x hw
    · change b _ = y
      simp only [map_add, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hbv]
      ring
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
      Module.finrank ℝ (ℝ × ℝ) := by simp [Module.finrank_prod]
  have hinj : Function.Injective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    fun _ => rfl⟩

theorem exists_local_coordinates_of_transverse_levels
    {f g : EuclideanSpace ℝ (Fin 2) → ℝ} {p v : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hdf : fderiv ℝ f p ≠ 0)
    (hvf : fderiv ℝ f p v = 0) (hvg : fderiv ℝ g p v ≠ 0) :
    ∃ F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ),
      p ∈ F.source ∧ (∀ z, F z = (f z, g z)) ∧
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ F.symm (f p, g p) := by
  obtain ⟨L, hL⟩ := exists_equiv_of_transverse_functionals hdf hvf hvg
  let H : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => (f z, g z)
  have hH : ContDiffAt ℝ ∞ H p := hf.prodMk hg
  have hdH : HasStrictFDerivAt H (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × ℝ)) p := by
    convert! (hf.hasStrictFDerivAt (by simp)).prodMk
      (hg.hasStrictFDerivAt (by simp)) using 1
    exact ContinuousLinearMap.ext hL
  let F := hdH.toOpenPartialHomeomorph H
  have hp : p ∈ F.source := hdH.mem_toOpenPartialHomeomorph_source
  have hFp : F p = (f p, g p) := rfl
  have hsymm : F.symm (f p, g p) = p := hFp ▸ F.left_inv hp
  refine ⟨F, hp, fun _ => rfl, hH, ?_⟩
  apply F.contDiffAt_symm (hFp ▸ F.map_source hp)
  · rw [hsymm]
    exact hdH.hasFDerivAt
  · rw [hsymm]
    exact hH

private theorem exists_rectangle_in_coordinates
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ))
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ F.source)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 p) :
    ∃ a b c d : ℝ,
      (F p).1 ∈ Ioo a b ∧ (F p).2 ∈ Ioo c d ∧
      (Ioo a b ×ˢ Ioo c d) ⊆ F.target ∧
      F.symm '' (Ioo a b ×ˢ Ioo c d) ⊆ s := by
  have htarget := F.map_source hp
  have hnbhd : F.target ∩ F.symm ⁻¹' s ∈ 𝓝 (F p) := by
    refine Filter.inter_mem (F.open_target.mem_nhds htarget) ?_
    apply (F.symm.continuousAt htarget).preimage_mem_nhds
    simpa only [F.left_inv hp] using hs
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hnbhd
  obtain ⟨a, b, hab, ha⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  obtain ⟨c, d, hcd, hc⟩ := mem_nhds_iff_exists_Ioo_subset.mp hB
  refine ⟨a, b, c, d, hab, hcd, ?_, ?_⟩
  · exact fun q hq => (hAB ⟨ha hq.1, hc hq.2⟩).1
  · rintro _ ⟨q, hq, rfl⟩
    exact (hAB ⟨ha hq.1, hc hq.2⟩).2

private def intervalSide (a x b : ℝ) (i : Bool) : Set ℝ :=
  if i then Ioo x b else Ioo a x

private theorem intervalSide_subset {a x b : ℝ} (hx : x ∈ Ioo a b) (i : Bool) :
    intervalSide a x b i ⊆ Ioo a b := by
  cases i <;> simp only [intervalSide, Bool.false_eq_true, ↓reduceIte]
  · exact fun _ h => ⟨h.1, h.2.trans hx.2⟩
  · exact fun _ h => ⟨hx.1.trans h.1, h.2⟩

private theorem intervalSide_open (a x b : ℝ) (i : Bool) :
    IsOpen (intervalSide a x b i) := by
  cases i <;> exact isOpen_Ioo

private theorem intervalSide_connected {a x b : ℝ} (hx : x ∈ Ioo a b) (i : Bool) :
    IsPathConnected (intervalSide a x b i) := by
  cases i
  · exact (convex_Ioo a x).isPathConnected (nonempty_Ioo.mpr hx.1)
  · exact (convex_Ioo x b).isPathConnected (nonempty_Ioo.mpr hx.2)

private theorem intervalSide_ne {a x b y : ℝ} {i : Bool}
    (hy : y ∈ intervalSide a x b i) : y ≠ x := by
  cases i
  · exact ne_of_lt hy.2
  · exact ne_of_gt hy.1

private theorem mem_intervalSide {a x b y : ℝ} (hy : y ∈ Ioo a b) (hne : y ≠ x) :
    ∃ i : Bool, y ∈ intervalSide a x b i := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨false, hy.1, h⟩
  · exact ⟨true, h, hy.2⟩

theorem exists_four_sectors_of_transverse_levels
    {f g : EuclideanSpace ℝ (Fin 2) → ℝ} {p v : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hdf : fderiv ℝ f p ≠ 0)
    (hvf : fderiv ℝ f p v = 0) (hvg : fderiv ℝ g p v ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 p) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 2)))
      (U : Bool × Bool → Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      (∀ i, IsOpen (U i) ∧ IsPathConnected (U i)) ∧
      (⋃ i, U i) = W \ ({z | f z = f p} ∪ {z | g z = g p}) := by
  obtain ⟨F, hp, hF, _, _⟩ :=
    exists_local_coordinates_of_transverse_levels hf hg hdf hvf hvg
  obtain ⟨a, b, c, d, hab, hcd, hbox, hsbox⟩ :=
    exists_rectangle_in_coordinates F hp hs
  rw [hF] at hab hcd
  let box := Ioo a b ×ˢ Ioo c d
  let Q (i : Bool × Bool) :=
    intervalSide a (f p) b i.1 ×ˢ intervalSide c (g p) d i.2
  have hQ (i : Bool × Bool) : Q i ⊆ box :=
    prod_mono (intervalSide_subset hab i.1) (intervalSide_subset hcd i.2)
  have hcoordinates (q : ℝ × ℝ) (hq : q ∈ box) :
      f (F.symm q) = q.1 ∧ g (F.symm q) = q.2 := by
    have h := F.right_inv (hbox hq)
    rw [hF] at h
    exact Prod.mk.inj h
  refine ⟨F.symm '' box, fun i => F.symm '' Q i,
    F.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox,
    ⟨F p, by simpa only [hF, box, mem_prod] using And.intro hab hcd, F.left_inv hp⟩,
    hsbox, ?_, ?_⟩
  · intro i
    exact ⟨F.symm.isOpen_image_of_subset_source
      ((intervalSide_open a (f p) b i.1).prod (intervalSide_open c (g p) d i.2))
      ((hQ i).trans hbox),
      ((intervalSide_connected hab i.1).prod (intervalSide_connected hcd i.2)).image'
        (F.symm.continuousOn.mono ((hQ i).trans hbox))⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, q, hq, rfl⟩
      have hco := hcoordinates q (hQ i hq)
      refine ⟨⟨q, hQ i hq, rfl⟩, ?_⟩
      simp only [mem_union, mem_ofPred_eq, hco.1, hco.2, not_or]
      exact ⟨intervalSide_ne hq.1, intervalSide_ne hq.2⟩
    · rintro ⟨⟨q, hq, rfl⟩, hnot⟩
      have hco := hcoordinates q hq
      simp only [mem_union, mem_ofPred_eq, hco.1, hco.2, not_or] at hnot
      obtain ⟨i, hi⟩ := mem_intervalSide hq.1 hnot.1
      obtain ⟨j, hj⟩ := mem_intervalSide hq.2 hnot.2
      exact mem_iUnion.mpr ⟨(i, j), q, ⟨hi, hj⟩, rfl⟩

theorem exists_finite_complement_of_transverse_levels
    {f g : EuclideanSpace ℝ (Fin 2) → ℝ} {p v : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p)
    (hdf : fderiv ℝ f p ≠ 0)
    (hvf : fderiv ℝ f p v = 0) (hvg : fderiv ℝ g p v ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 p) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      Finite (ConnectedComponents
        (W \ ({z | f z = f p} ∪ {z | g z = g p}) : Set (EuclideanSpace ℝ (Fin 2)))) := by
  obtain ⟨W, U, hopen, hp, hsub, hU, hcover⟩ :=
    exists_four_sectors_of_transverse_levels hf hg hdf hvf hvg hs
  exact ⟨W, hopen, hp, hsub,
    Poincare.Topology.finite_connectedComponents_of_finite_preconnected_cover_set U
      (fun i => (hU i).2.isConnected.isPreconnected) hcover⟩

theorem exists_local_coordinates_of_regular_level
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hdf : fderiv ℝ f p ≠ 0) :
    ∃ F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (ℝ × ℝ),
      p ∈ F.source ∧ (∀ z, (F z).1 = f z) ∧
      ContDiffAt ℝ ∞ F p ∧ ContDiffAt ℝ ∞ F.symm (F p) := by
  have hlin : (fderiv ℝ f p).toLinearMap ≠ 0 := by
    intro h
    apply hdf
    ext x
    exact congrArg (fun L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => L x) h
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hlin
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker (fderiv ℝ f p).toLinearMap) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hdim
    omega
  have : Nontrivial (LinearMap.ker (fderiv ℝ f p).toLinearMap) :=
    Module.finrank_pos_iff.mp hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : LinearMap.ker (fderiv ℝ f p).toLinearMap)
  have hvne : (v : EuclideanSpace ℝ (Fin 2)) ≠ 0 := fun h => hv (Subtype.ext h)
  let g : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ (v : EuclideanSpace ℝ (Fin 2))
  have hvg : fderiv ℝ g p v ≠ 0 := by
    rw [g.fderiv]
    exact inner_self_ne_zero.mpr hvne
  obtain ⟨F, hp, hF, hcont, hinv⟩ :=
    exists_local_coordinates_of_transverse_levels hf g.contDiff.contDiffAt
      hdf v.property hvg
  refine ⟨F, hp, fun z => congrArg Prod.fst (hF z), hcont, ?_⟩
  simpa only [hF] using hinv

theorem exists_two_sectors_of_regular_level
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hdf : fderiv ℝ f p ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 p) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 2)))
      (U : Bool → Set (EuclideanSpace ℝ (Fin 2))),
      IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      (∀ i, IsOpen (U i) ∧ IsPathConnected (U i)) ∧
      (⋃ i, U i) = W \ {z | f z = f p} := by
  obtain ⟨F, hp, hF, _, _⟩ := exists_local_coordinates_of_regular_level hf hdf
  obtain ⟨a, b, c, d, hab, hcd, hbox, hsbox⟩ :=
    exists_rectangle_in_coordinates F hp hs
  rw [hF] at hab
  let box := Ioo a b ×ˢ Ioo c d
  let Q (i : Bool) := intervalSide a (f p) b i ×ˢ Ioo c d
  have hQ (i : Bool) : Q i ⊆ box :=
    prod_mono (intervalSide_subset hab i) (Subset.refl _)
  have hcoordinate (q : ℝ × ℝ) (hq : q ∈ box) : f (F.symm q) = q.1 := by
    rw [← hF, F.right_inv (hbox hq)]
  refine ⟨F.symm '' box, fun i => F.symm '' Q i,
    F.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox,
    ⟨F p, ⟨by simpa only [hF] using hab, hcd⟩, F.left_inv hp⟩,
    hsbox, ?_, ?_⟩
  · intro i
    exact ⟨F.symm.isOpen_image_of_subset_source
      ((intervalSide_open a (f p) b i).prod isOpen_Ioo) ((hQ i).trans hbox),
      ((intervalSide_connected hab i).prod
        ((convex_Ioo c d).isPathConnected ⟨(F p).2, hcd⟩)).image'
        (F.symm.continuousOn.mono ((hQ i).trans hbox))⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, q, hq, rfl⟩
      refine ⟨⟨q, hQ i hq, rfl⟩, ?_⟩
      simpa only [mem_ofPred_eq, hcoordinate q (hQ i hq)] using intervalSide_ne hq.1
    · rintro ⟨⟨q, hq, rfl⟩, hnot⟩
      simp only [mem_ofPred_eq, hcoordinate q hq] at hnot
      obtain ⟨i, hi⟩ := mem_intervalSide hq.1 hnot
      exact mem_iUnion.mpr ⟨i, q, ⟨hi, hq.2⟩, rfl⟩

theorem exists_finite_complement_of_regular_level
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hf : ContDiffAt ℝ ∞ f p) (hdf : fderiv ℝ f p ≠ 0)
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : s ∈ 𝓝 p) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen W ∧ p ∈ W ∧ W ⊆ s ∧
      Finite (ConnectedComponents
        (W \ {z | f z = f p} : Set (EuclideanSpace ℝ (Fin 2)))) := by
  obtain ⟨W, U, hopen, hp, hsub, hU, hcover⟩ :=
    exists_two_sectors_of_regular_level hf hdf hs
  exact ⟨W, hopen, hp, hsub,
    Poincare.Topology.finite_connectedComponents_of_finite_preconnected_cover_set U
      (fun i => (hU i).2.isConnected.isPreconnected) hcover⟩

end Poincare.Topology.Plane.Curves
