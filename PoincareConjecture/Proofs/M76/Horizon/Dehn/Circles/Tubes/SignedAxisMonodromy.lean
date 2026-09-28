import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisPermutations
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PairedTubeSigns











set_option autoImplicit false
open Set Geometry

namespace Polygon


theorem transverse_strip_side_labels {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    {f : (ℝ × ℝ) → (ℝ × ℝ)}
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn f (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ x ∈ Icc (-r) r ×ˢ Icc a b, f x ∈ P.boundary ℝ ↔ x.1 = 0) :
    (f '' (Ioc 0 r ×ˢ Icc a b) ⊆ P.inside ∧
      f '' (Ico (-r) 0 ×ˢ Icc a b) ⊆ P.outside) ∨
    (f '' (Ico (-r) 0 ×ˢ Icc a b) ⊆ P.inside ∧
      f '' (Ioc 0 r ×ˢ Icc a b) ⊆ P.outside) := by
  let S := Icc (-r) r ×ˢ Icc a b
  let A := Ioc 0 r ×ˢ Icc a b
  let B := Ico (-r) 0 ×ˢ Icc a b
  have hAS : A ⊆ S := fun x hx ↦
    ⟨⟨(neg_nonpos.mpr hr.le).trans hx.1.1.le, hx.1.2⟩, hx.2⟩
  have hBS : B ⊆ S := fun x hx ↦
    ⟨⟨hx.1.1, hx.1.2.le.trans hr.le⟩, hx.2⟩
  have hA : IsPreconnected (f '' A) :=
    (isPreconnected_Ioc.prod isPreconnected_Icc).image f (hf.continuousOn.mono hAS)
  have hB : IsPreconnected (f '' B) :=
    (isPreconnected_Ico.prod isPreconnected_Icc).image f (hf.continuousOn.mono hBS)
  have hcomp : f '' A ∪ f '' B ⊆ (P.boundary ℝ)ᶜ := by
    rintro y (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) hy
    · exact hx.1.1.ne' ((haxis x (hAS hx)).mp hy)
    · exact hx.1.2.ne ((haxis x (hBS hx)).mp hy)
  let q : ℝ × ℝ := (0, (a + b) / 2)
  have hq : q ∈ Ioo (-r) r ×ˢ Ioo a b := by
    dsimp [q]
    constructor <;> constructor <;> linarith
  obtain ⟨K, hK, hconv, hqK, hKsub⟩ :=
    (isOpen_Ioo.prod isOpen_Ioo).exists_finite_convex_neighborhood hq
  have hKS : K.space ⊆ S := fun x hx ↦
    ⟨⟨(hKsub hx).1.1.le, (hKsub hx).1.2.le⟩,
      (hKsub hx).2.1.le, (hKsub hx).2.2.le⟩
  have hqU : f q ∈ interior (f '' K.space) :=
    (hf.restrict K hK hKS).mem_interior_image_of_convex hconv rfl
      (hinj.mono hKsub) hqK
  have hqP : f q ∈ P.boundary ℝ :=
    (haxis q (hKS (interior_subset hqK))).mpr rfl
  have hcover : interior (f '' K.space) \ P.boundary ℝ ⊆ f '' A ∪ f '' B := by
    rintro y ⟨hy, hyP⟩
    obtain ⟨x, hxK, rfl⟩ := interior_subset hy
    have hx := hKS hxK
    have hx0 : x.1 ≠ 0 := fun heq ↦ hyP ((haxis x hx).mpr heq)
    rcases lt_or_gt_of_ne hx0 with hn | hp
    · exact Or.inr ⟨x, ⟨⟨hx.1.1, hn⟩, hx.2⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨⟨hp, hx.1.2⟩, hx.2⟩, rfl⟩
  have hsideA := hA.subset_or_subset (P.isOpen_inside hP hinjP)
    (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
    ((subset_union_left.trans hcomp).trans P.compl_boundary_eq_inside_union_outside.subset)
  have hsideB := hB.subset_or_subset (P.isOpen_inside hP hinjP)
    (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
    ((subset_union_right.trans hcomp).trans P.compl_boundary_eq_inside_union_outside.subset)
  rcases hsideA with hAi | hAo <;> rcases hsideB with hBi | hBo
  · have hqcl : f q ∈ closure P.outside :=
      frontier_subset_closure ((P.frontier_outside hP hinjP).symm ▸ hqP)
    obtain ⟨z, hzU, hzO⟩ := mem_closure_iff.mp hqcl _ isOpen_interior hqU
    exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside
      ((hcover ⟨hzU, hzO.1⟩).elim (fun h ↦ hAi h) (fun h ↦ hBi h)) hzO)
  · exact Or.inl ⟨hAi, hBo⟩
  · exact Or.inr ⟨hBi, hAo⟩
  · have hqcl : f q ∈ closure P.inside :=
      frontier_subset_closure ((P.frontier_inside hP hinjP).symm ▸ hqP)
    obtain ⟨z, hzU, hzI⟩ := mem_closure_iff.mp hqcl _ isOpen_interior hqU
    exact False.elim (Set.disjoint_left.mp P.disjoint_inside_outside hzI
      ((hcover ⟨hzU, hzI.1⟩).elim (fun h ↦ hAo h) (fun h ↦ hBo h)))


theorem exchanged_strip_signs_eq {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    (phi : Fin 2 → (ℝ × ℝ) → (ℝ × ℝ))
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn (phi 0) (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ j x, x ∈ Icc (-r) r ×ˢ Icc a b →
      (phi j x ∈ P.boundary ℝ ↔ x.1 = 0))
    (sign : Fin 2 → Bool)
    (hclose : ∀ (j : Fin 2) u, u ∈ Icc (-r) r →
      phi j (u, a) = phi j.rev ((if sign j.rev then u else -u), b)) :
    sign 0 = sign 1 := by
  let A := phi 0 '' (Ioc 0 r ×ˢ Icc a b)
  let B := phi 0 '' (Ico (-r) 0 ×ˢ Icc a b)
  let Z := phi 1 '' (Ioc 0 r ×ˢ Icc a b)
  have hhalf : Ioc 0 r ×ˢ Icc a b ⊆ Icc (-r) r ×ˢ Icc a b := by
    intro x hx
    exact ⟨⟨(neg_nonpos.mpr hr.le).trans hx.1.1.le, hx.1.2⟩, hx.2⟩
  have hZ : IsPreconnected Z :=
    (isPreconnected_Ioc.prod isPreconnected_Icc).image (phi 1)
      ((hPL 1).continuousOn.mono hhalf)
  have hZcomp : Z ⊆ (P.boundary ℝ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ h
    exact hx.1.1.ne' ((haxis 1 x (hhalf hx)).mp h)
  have hZside := hZ.subset_or_subset (P.isOpen_inside hP hinjP)
    (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
    (hZcomp.trans P.compl_boundary_eq_inside_union_outside.subset)
  have hsides := P.transverse_strip_side_labels hP hinjP hr hab (hPL 0) hinj (haxis 0)
  have hno (p q : ℝ × ℝ) (hpA : p ∈ A) (hpZ : p ∈ Z)
      (hqB : q ∈ B) (hqZ : q ∈ Z) : False := by
    rcases hsides with ⟨hAi, hBo⟩ | ⟨hBi, hAo⟩ <;> rcases hZside with hZi | hZo
    · exact Set.disjoint_left.mp P.disjoint_inside_outside (hZi hqZ) (hBo hqB)
    · exact Set.disjoint_left.mp P.disjoint_inside_outside (hAi hpA) (hZo hpZ)
    · exact Set.disjoint_left.mp P.disjoint_inside_outside (hZi hpZ) (hAo hpA)
    · exact Set.disjoint_left.mp P.disjoint_inside_outside (hBi hqB) (hZo hqZ)
  have hrI : r ∈ Icc (-r) r := ⟨by linarith, le_rfl⟩
  have hnrI : -r ∈ Icc (-r) r := ⟨le_rfl, by linarith⟩
  have hAa : phi 0 (r, a) ∈ A := ⟨(r, a), ⟨⟨hr, le_rfl⟩, le_rfl, hab.le⟩, rfl⟩
  have hAb : phi 0 (r, b) ∈ A := ⟨(r, b), ⟨⟨hr, le_rfl⟩, hab.le, le_rfl⟩, rfl⟩
  have hBa : phi 0 (-r, a) ∈ B :=
    ⟨(-r, a), ⟨⟨le_rfl, neg_lt_zero.mpr hr⟩, le_rfl, hab.le⟩, rfl⟩
  have hBb : phi 0 (-r, b) ∈ B :=
    ⟨(-r, b), ⟨⟨le_rfl, neg_lt_zero.mpr hr⟩, hab.le, le_rfl⟩, rfl⟩
  have hZa : phi 1 (r, a) ∈ Z := ⟨(r, a), ⟨⟨hr, le_rfl⟩, le_rfl, hab.le⟩, rfl⟩
  have hZb : phi 1 (r, b) ∈ Z := ⟨(r, b), ⟨⟨hr, le_rfl⟩, hab.le, le_rfl⟩, rfl⟩
  cases h0 : sign 0 <;> cases h1 : sign 1
  · rfl
  · have hc0 : phi 0 (r, a) = phi 1 (r, b) := by
      simpa [Fin.rev, h1] using hclose 0 r hrI
    have hc1 : phi 1 (r, a) = phi 0 (-r, b) := by
      simpa [Fin.rev, h0] using hclose 1 r hrI
    exact (hno _ _ hAa (hc0.symm ▸ hZb) hBb (hc1 ▸ hZa)).elim
  · have hc0 : phi 0 (-r, a) = phi 1 (r, b) := by
      simpa [Fin.rev, h1] using hclose 0 (-r) hnrI
    have hc1 : phi 1 (r, a) = phi 0 (r, b) := by
      simpa [Fin.rev, h0] using hclose 1 r hrI
    exact (hno _ _ hAb (hc1 ▸ hZa) hBa (hc0.symm ▸ hZb)).elim
  · rfl

end Polygon

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)



theorem signed_axis_closing_swaps_of_connected_source
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (closing : SignedAxisPermutation) {a b : ℝ} (hab : a < b)
    (axis : Fin 2 → ℝ → X) (haxis : ∀ j, ContinuousOn (axis j) (Icc a b))
    (C : Set X) (hC : IsPreconnected C)
    (hcover : C = axis 0 '' Icc a b ∪ axis 1 '' Icc a b)
    (hfib : ∀ (j k : Fin 2) s, s ∈ Icc a b → ∀ t, t ∈ Icc a b →
      (axis j s = axis k t ↔ (j = k ∧ s = t) ∨
        (s = a ∧ t = b ∧ k = closing.index j) ∨
        (t = a ∧ s = b ∧ j = closing.index k))) :
    closing.swap = true := by
  cases hs : closing.swap with
  | true => rfl
  | false =>
    have hcompact (j : Fin 2) := isCompact_Icc.image_of_continuousOn (haxis j)
    have h0 : axis 0 a ∈ axis 0 '' Icc a b := ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
    have h1 : axis 1 a ∈ axis 1 '' Icc a b := ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
    obtain ⟨x, _, ⟨s, hsI, hsx⟩, ⟨t, htI, htx⟩⟩ :=
      isPreconnected_closed_iff.mp hC _ _ (hcompact 0).isClosed (hcompact 1).isClosed
        hcover.subset ⟨axis 0 a, hcover.symm ▸ Or.inl h0, h0⟩
        ⟨axis 1 a, hcover.symm ▸ Or.inr h1, h1⟩
    have h := (hfib 0 1 s hsI t htI).mp (hsx.trans htx.symm)
    simp [SignedAxisPermutation.index, jointSheetIndex, hs] at h


theorem exchanged_source_strip_signs_eq {n : ℕ}
    (P : Polygon V2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    (phi : Fin 2 → P2 → V2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn (phi 0) (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ j x, x ∈ Icc (-r) r ×ˢ Icc a b →
      (phi j x ∈ P.boundary ℝ ↔ x.1 = 0))
    (sign : Fin 2 → Bool)
    (hclose : ∀ (j : Fin 2) u, u ∈ Icc (-r) r →
      phi j (u, a) = phi j.rev ((if sign j.rev then u else -u), b)) :
    sign 0 = sign 1 := by
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let Q := P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap
  have hQ := P.affineImage_of_leftInvOn hP hinjP
    e.toLinearEquiv.toAffineEquiv.toAffineMap
    e.symm.toLinearEquiv.toAffineEquiv.toAffineMap (fun _ _ ↦ e.symm_apply_apply _)
  apply Q.exchanged_strip_signs_eq hQ.2.1 hQ.1 hr hab (fun j ↦ e ∘ phi j)
    (fun j ↦ (hPL j).postcomp e.toContinuousLinearMap.toContinuousAffineMap)
    (fun _ hx _ hy hxy ↦ hinj hx hy (e.injective hxy)) ?_ sign
    (fun j u hu ↦ congrArg e (hclose j u hu))
  intro j x hx
  change e (phi j x) ∈ (P.affineImage _).boundary ℝ ↔ x.1 = 0
  rw [P.affineImage_boundary]
  exact e.injective.mem_set_image.trans (haxis j x hx)



theorem signed_axis_closing_classification_from_source_strips {n : ℕ}
    (P : Polygon V2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    (phi : Fin 2 → P2 → V2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-r) r ×ˢ Icc a b))
    (hinj : ∀ j, InjOn (phi j) (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ j x, x ∈ Icc (-r) r ×ˢ Icc a b →
      (phi j x ∈ P.boundary ℝ ↔ x.1 = 0))
    (closing : SignedAxisPermutation)
    (hclose : ∀ (j : Fin 2) u, u ∈ Icc (-r) r →
      phi j (u, a) = phi (closing.index j)
        ((if closing.sign j.rev then u else -u), b)) :
    closing = SignedAxisPermutation.refl ∨
      (closing.swap = true ∧ closing.sign 0 = closing.sign 1) := by
  cases hs : closing.swap with
  | false =>
    have hsign (j : Fin 2) : closing.sign j.rev = true :=
      P.strip_closing_sign_eq_true_in_coordinates (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
        hP hinjP hr hab (hPL j) (hinj j) (haxis j) (closing.sign j.rev)
        (by simpa [SignedAxisPermutation.index, jointSheetIndex, hs] using
          hclose j r ⟨by linarith, le_rfl⟩)
    refine Or.inl (SignedAxisPermutation.ext hs ?_)
    funext j
    simpa [SignedAxisPermutation.refl] using hsign j.rev
  | true =>
    refine Or.inr ⟨rfl, exchanged_source_strip_signs_eq P hP hinjP hr hab
      phi hPL (hinj 0) haxis closing.sign ?_⟩
    intro j u hu
    simpa [SignedAxisPermutation.index, jointSheetIndex, hs] using hclose j u hu



theorem signed_axis_closing_eq_refl_of_paired_sheets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a < b) (sigma : P2 × ℝ → E) (closing : SignedAxisPermutation)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          closing.linear (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          closing.linear (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (S : Fin 2 → Set E) (C : Fin 2 → Set V2) (A : Set E)
    (u : ∀ j, S j ≃ₜ C j) (hu : ∀ j, (u j).IsFinitePL)
    (n : Fin 2 → ℕ) (P : ∀ j, Polygon V2 (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hinjP : ∀ j, Function.Injective (P j))
    (hsheet : ∀ j (x : ↥(signedTubeDiamond ×ˢ Icc a b)),
      sigma x ∈ S j ↔ (x : P2 × ℝ).1 ∈ signedTubeSheet j)
    (haxis : ∀ x : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x ∈ A ↔ (x : P2 × ℝ).1 = (0, 0))
    (huaxis : ∀ j (z : S j), (u j z : V2) ∈ (P j).boundary ℝ ↔ (z : E) ∈ A) :
    closing = SignedAxisPermutation.refl := by
  have hc : ((0, 1) : P2) ∈ signedTubeDiamond := by
    rw [signedTubeDiamond_coordinate_iff]
    norm_num
  have hx : (((0, 1) : P2), a) ∈ signedTubeDiamond ×ˢ Icc a b :=
    ⟨hc, le_rfl, hab.le⟩
  have hy : (closing.linear (0, 1), b) ∈ signedTubeDiamond ×ˢ Icc a b :=
    ⟨(closing.mem_diamond _).mp hc, hab.le, le_rfl⟩
  have heq : sigma ((0, 1), a) = sigma (closing.linear (0, 1), b) :=
    (hfib ⟨_, hx⟩ ⟨_, hy⟩).mpr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have hleft : sigma ((0, 1), a) ∈ S 0 :=
    (hsheet 0 ⟨_, hx⟩).mpr ((signedTubeSheet_coordinate_iff _ hc 0).mpr rfl)
  have hz := (signedTubeSheet_coordinate_iff _ hy.1 0).mp
    ((hsheet 0 ⟨_, hy⟩).mp (heq ▸ hleft))
  have hswap : closing.swap = false := by
    cases hs : closing.swap with
    | false => rfl
    | true =>
      cases hsign : closing.sign 1 <;>
        simp [SignedAxisPermutation.linear_apply, hs, hsign] at hz
  have hlinear (x : P2) : closing.linear x = signedTubeReflection closing.sign x := by
    simp [SignedAxisPermutation.linear_apply, hswap, signedTubeReflection_apply]
  have hsign := signed_diamond_closing_eq_true hab sigma closing.sign hPL
    (fun x y ↦ by simpa only [hlinear] using hfib x y)
    S C A u hu n P hP hinjP hsheet haxis huaxis
  exact SignedAxisPermutation.ext hswap (funext hsign)

namespace SignedAxisPermutation



def reflectionFrame (a : SignedAxisPermutation) : SignedAxisPermutation :=
  ⟨false, ![true, a.sign 0]⟩

theorem reflectionFrame_conjugate (a : SignedAxisPermutation)
    (hswap : a.swap = true) (hsign : a.sign 0 = a.sign 1) (x : P2) :
    a.linear (a.reflectionFrame.linear x) = a.reflectionFrame.linear (x.2, x.1) := by
  cases h0 : a.sign 0 <;>
    simp [linear_apply, reflectionFrame, hswap, ← hsign, h0]


noncomputable def reflectionCoordinates (a : SignedAxisPermutation) : P2 ≃L[ℝ] P2 :=
  signedSquareToDiamond.trans a.reflectionFrame.linear

theorem reflectionCoordinates_conjugate (a : SignedAxisPermutation)
    (hswap : a.swap = true) (hsign : a.sign 0 = a.sign 1) (x : P2) :
    a.linear (a.reflectionCoordinates x) = a.reflectionCoordinates (x.1, -x.2) := by
  change a.linear (a.reflectionFrame.linear (signedSquareToDiamond x)) =
    a.reflectionFrame.linear (signedSquareToDiamond (x.1, -x.2))
  rw [a.reflectionFrame_conjugate hswap hsign]
  congr 1
  ext <;> simp [signedSquareToDiamond_apply, sub_eq_add_neg]

theorem reflectionCoordinates_mem (a : SignedAxisPermutation) (x : P2) :
    a.reflectionCoordinates x ∈ signedTubeDiamond ↔
      x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
  (a.reflectionFrame.mem_diamond (signedSquareToDiamond x)).symm.trans
    (signedSquareToDiamond_mem x)

end SignedAxisPermutation

end PoincareConjecture.M76.Dehn
