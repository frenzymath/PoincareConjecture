import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.PlanarMonodromy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.BranchInverses
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.ModelArc
import PoincareConjecture.Proofs.M76.Mathlib.HeightBoxGeometry










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

noncomputable def signedSheetStripMap (j : Fin 2) : P2 →L[ℝ] P2 × ℝ :=
  if j = 0 then
    ((0 : P2 →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  else
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (0 : P2 →L[ℝ] ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem signedSheetStripMap_apply (j : Fin 2) (x : P2) :
    signedSheetStripMap j x = ((if j = 0 then (0, x.1) else (x.1, 0)), x.2) := by
  fin_cases j <;> rfl

theorem signedSheetStripMap_mem {a b : ℝ} (j : Fin 2)
    {x : P2} (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
    signedSheetStripMap j x ∈ signedTubeDiamond ×ˢ Icc a b := by
  rw [signedSheetStripMap_apply]
  refine ⟨?_, hx.2⟩
  rw [signedTubeDiamond_coordinate_iff]
  fin_cases j <;> simpa using (abs_le.mpr hx.1)

theorem signedSheetStripMap_sheet {a b : ℝ} (j : Fin 2)
    {x : P2} (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
    (signedSheetStripMap j x).1 ∈ signedTubeSheet j := by
  rw [signedTubeSheet_coordinate_iff _ (signedSheetStripMap_mem j hx).1]
  fin_cases j <;> simp [signedSheetStripMap_apply]

theorem signedSheetStripMap_finitePL {a b : ℝ} (hab : a < b) (j : Fin 2) :
    FinitePiecewiseAffineOn (signedSheetStripMap j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    HeightBox.rectangle_ballPair (show (0 : ℝ) < 1 by norm_num) hab
  exact ⟨K, hK, hKs, K.affineOnFaces_affine
    (signedSheetStripMap j).toContinuousAffineMap⟩



theorem signed_diamond_closing_eq_true
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a < b) (sigma : P2 × ℝ → E) (closing : Fin 2 → Bool)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (S : Fin 2 → Set E) (C : Fin 2 → Set V2) (A : Set E)
    (u : ∀ j, S j ≃ₜ C j) (hu : ∀ j, (u j).IsFinitePL)
    (n : Fin 2 → ℕ) (P : ∀ j, Polygon V2 (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hinjP : ∀ j, Function.Injective (P j))
    (hsheet : ∀ j (x : ↥(signedTubeDiamond ×ˢ Icc a b)),
      sigma x ∈ S j ↔ (x : P2 × ℝ).1 ∈ signedTubeSheet j)
    (haxis : ∀ x : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x ∈ A ↔ (x : P2 × ℝ).1 = (0, 0))
    (huaxis : ∀ j (z : S j), (u j z : V2) ∈ (P j).boundary ℝ ↔ (z : E) ∈ A) :
    ∀ j, closing j = true := by
  have hsign (j : Fin 2) : closing j.rev = true := by
    obtain ⟨v, hv, hvalue⟩ := hu j
    let f : P2 → V2 := v ∘ sigma ∘ signedSheetStripMap j
    have hS (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
        sigma (signedSheetStripMap j x) ∈ S j :=
      (hsheet j ⟨_, signedSheetStripMap_mem j hx⟩).mpr (signedSheetStripMap_sheet j hx)
    have hfv (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
        f x = (u j ⟨sigma (signedSheetStripMap j x), hS x hx⟩ : V2) :=
      (hvalue ⟨sigma (signedSheetStripMap j x), hS x hx⟩).symm
    have hf : FinitePiecewiseAffineOn f (Icc (-1 : ℝ) 1 ×ˢ Icc a b) :=
      hv.comp (hPL.comp (signedSheetStripMap_finitePL hab j)
        (fun _ hx => signedSheetStripMap_mem j hx)) hS
    have hi : InjOn f (Ioo (-1 : ℝ) 1 ×ˢ Ioo a b) := by
      intro x hx y hy hxy
      have hx' : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
        ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2.1.le, hx.2.2.le⟩
      have hy' : y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
        ⟨⟨hy.1.1.le, hy.1.2.le⟩, hy.2.1.le, hy.2.2.le⟩
      have hz : sigma (signedSheetStripMap j x) = sigma (signedSheetStripMap j y) := by
        rw [hfv x hx', hfv y hy'] at hxy
        exact congrArg Subtype.val ((u j).injective (Subtype.ext hxy))
      rcases (hfib ⟨_, signedSheetStripMap_mem j hx'⟩
        ⟨_, signedSheetStripMap_mem j hy'⟩).mp hz with heq | heq | heq
      · have heq' := congrArg Subtype.val heq
        apply Prod.ext
        · have hh := congrArg (fun z : P2 × ℝ => if j = 0 then z.1.2 else z.1.1) heq'
          fin_cases j <;> simpa [signedSheetStripMap_apply] using hh
        · simpa [signedSheetStripMap_apply] using congrArg Prod.snd heq'
      · exact (hx.2.1.ne' (by simpa [signedSheetStripMap_apply] using heq.1)).elim
      · exact (hy.2.1.ne' (by simpa [signedSheetStripMap_apply] using heq.1)).elim
    have hfa (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
        f x ∈ (P j).boundary ℝ ↔ x.1 = 0 := by
      rw [hfv x hx, huaxis j, haxis ⟨_, signedSheetStripMap_mem j hx⟩]
      fin_cases j <;> simp [signedSheetStripMap_apply]
    have hc : f (1, a) = f ((if closing j.rev then 1 else -1), b) := by
      have hx : (1, a) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
        ⟨⟨by norm_num, le_rfl⟩, le_rfl, hab.le⟩
      have hy : ((if closing j.rev then 1 else -1), b) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b := by
        constructor
        · split <;> norm_num
        · exact ⟨hab.le, le_rfl⟩
      apply congrArg v
      apply (hfib ⟨_, signedSheetStripMap_mem j hx⟩
        ⟨_, signedSheetStripMap_mem j hy⟩).mpr
      apply Or.inr ∘ Or.inl
      refine ⟨by simp [signedSheetStripMap_apply], by simp [signedSheetStripMap_apply], ?_⟩
      fin_cases j <;> simp [signedSheetStripMap_apply, signedTubeReflection_apply,
        Fin.rev]
    exact (P j).strip_closing_sign_eq_true_in_coordinates
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) (hP j) (hinjP j)
      (by norm_num) hab hf hi hfa (closing j.rev) hc
  intro j
  simpa using hsign j.rev

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}



theorem OrdinaryIntervalMarkedModel.branch_inverse_selected_iff
    (D : OrdinaryIntervalMarkedModel old i)
    (u : ∀ j : Fin 2, (D.marks (.inr j.castSucc)).space ≃ₜ (D.clips j.castSucc).space)
    (hu : ∀ (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space),
      f (u j z) = (D.inverse z : X))
    (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space) :
    (u j z : V2) ∈ old.pieces (if j = 0 then i else old.mate i) ↔
      (z : D.sample → ℝ × V3) ∈ (D.marks (.inr 2)).space := by
  have htrace := D.mem_mark_image (D.marks_image 2) z
    (SimplicialComplex.space_subset_of_le (D.marks_full (.inr j.castSucc)).1 z.property)
  rw [D.selected_source, ← hu j z] at htrace
  have hsource : (u j z : V2) ∈ (D.source j.castSucc).space := by
    exact ((D.clips_data j.castSucc).2.1.subset (u j z).property).1
  have himage : f '' old.pieces (if j = 0 then i else old.mate i) =
      f '' old.pieces i := by
    fin_cases j
    · rfl
    · exact old.piece_image_mate i
  have hcontains : old.pieces (if j = 0 then i else old.mate i) ⊆
      (D.source j.castSucc).space := by
    fin_cases j
    · exact D.left_contains
    · exact D.right_contains
  have hinj : InjOn f (D.source j.castSucc).space := by
    have hh : Topology.IsEmbedding (fun x : (D.source j.castSucc).space => f x) := by
      fin_cases j
      · exact D.left_embedding
      · exact D.right_embedding
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  rw [htrace]
  constructor
  · exact fun hx => himage.subset (mem_image_of_mem f hx)
  · intro hx
    obtain ⟨w, hw, hval⟩ := himage.symm.subset hx
    exact hinj (hcontains hw) hsource hval ▸ hw




theorem OrdinaryIntervalMarkedModel.exists_paired_source_strips
    (D : OrdinaryIntervalMarkedModel old i) {a b : ℝ} (hab : a < b)
    (sigma : P2 × ℝ → (D.sample → ℝ × V3)) (closing : Fin 2 → Bool)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b))
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          signedTubeReflection closing (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (n : Fin 2 → ℕ) (P : ∀ j, Polygon V2 (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hinjP : ∀ j, Function.Injective (P j))
    (hboundary : ∀ j, (P j).boundary ℝ = old.pieces (if j = 0 then i else old.mate i))
    (hsheet : ∀ (j : Fin 2) (x : ↥(signedTubeDiamond ×ˢ Icc a b)),
      sigma x ∈ (D.marks (.inr j.castSucc)).space ↔
        (x : P2 × ℝ).1 ∈ signedTubeSheet j)
    (haxis : ∀ x : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x ∈ (D.marks (.inr 2)).space ↔ (x : P2 × ℝ).1 = (0, 0)) :
    ∃ phi : Fin 2 → P2 → V2,
      (∀ j, closing j = true) ∧
      (∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) ∧
      (∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, phi j x ∈ (D.clips j.castSucc).space) ∧
      (∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
        f (phi j x) = (D.inverse (sigma (signedSheetStripMap j x)) : X)) ∧
      (∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
        D.graph (f (phi j x)) = sigma (signedSheetStripMap j x)) ∧
      (∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
        phi j x ∈ (P j).boundary ℝ ↔ x.1 = 0) ∧
      ∀ j, ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b, ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b,
        phi j x = phi j y ↔ x.1 = y.1 ∧
          (x.2 = y.2 ∨ (x.2 = a ∧ y.2 = b) ∨ (y.2 = a ∧ x.2 = b)) := by
  classical
  obtain ⟨u, hu, huvalue, hugraph, _, _, _⟩ := D.exists_branch_inverses
  have hucircle (j : Fin 2) (z : (D.marks (.inr j.castSucc)).space) :
      (u j z : V2) ∈ (P j).boundary ℝ ↔
        (z : D.sample → ℝ × V3) ∈ (D.marks (.inr 2)).space := by
    rw [hboundary j]
    exact D.branch_inverse_selected_iff u huvalue j z
  have hclosing := signed_diamond_closing_eq_true hab sigma closing hPL hfib
    (fun j : Fin 2 => (D.marks (.inr j.castSucc)).space)
    (fun j : Fin 2 => (D.clips j.castSucc).space) (D.marks (.inr 2)).space
    u (fun j => (hu j).1) n P hP hinjP hsheet haxis hucircle
  choose v hv hvalue using fun j => (hu j).1
  let phi : Fin 2 → P2 → V2 := fun j => v j ∘ sigma ∘ signedSheetStripMap j
  have hS (j : Fin 2) (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
      sigma (signedSheetStripMap j x) ∈ (D.marks (.inr j.castSucc)).space :=
    (hsheet j ⟨_, signedSheetStripMap_mem j hx⟩).mpr (signedSheetStripMap_sheet j hx)
  have hphi (j : Fin 2) (x : P2) (hx : x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) :
      phi j x = (u j ⟨sigma (signedSheetStripMap j x), hS j x hx⟩ : V2) :=
    (hvalue j ⟨sigma (signedSheetStripMap j x), hS j x hx⟩).symm
  refine ⟨phi, hclosing, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hv j).comp (hPL.comp (signedSheetStripMap_finitePL hab j)
      (fun _ hx => signedSheetStripMap_mem j hx)) (hS j)
  · intro j x hx
    rw [hphi j x hx]
    exact (u j ⟨_, hS j x hx⟩).property
  · intro j x hx
    rw [hphi j x hx]
    exact huvalue j _
  · intro j x hx
    rw [hphi j x hx]
    exact hugraph j _
  · intro j x hx
    rw [hphi j x hx, hucircle, haxis ⟨_, signedSheetStripMap_mem j hx⟩]
    fin_cases j <;> simp [signedSheetStripMap_apply]
  · intro j x hx y hy
    have heq : phi j x = phi j y ↔
        sigma (signedSheetStripMap j x) = sigma (signedSheetStripMap j y) := by
      rw [hphi j x hx, hphi j y hy]
      constructor
      · intro h
        exact congrArg Subtype.val ((u j).injective (Subtype.ext h))
      · intro h
        exact congrArg (fun z => (u j z : V2)) (Subtype.ext h)
    rw [heq, hfib ⟨_, signedSheetStripMap_mem j hx⟩ ⟨_, signedSheetStripMap_mem j hy⟩]
    simp only [Subtype.ext_iff, signedTubeReflection_apply, hclosing, ↓reduceIte,
      one_mul, signedSheetStripMap_apply]
    fin_cases j <;> simp [Prod.mk.injEq, and_or_left, and_comm, and_assoc, eq_comm]

end PoincareConjecture.M76.Dehn
