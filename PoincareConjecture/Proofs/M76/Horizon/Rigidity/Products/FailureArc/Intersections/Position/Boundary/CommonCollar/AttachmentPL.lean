import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentContinuity
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FiniteBaseIntervalProducts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLClosedUnion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_finite_interval_cylinder
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite) {a b : ℝ} (hab : a < b) :
    ∃ J : SimplicialComplex ℝ (ℝ × Z), J.faces.Finite ∧ J.space = Icc a b ×ˢ A.space := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨I, hI, hIs, _⟩, _⟩, _⟩ := isFinitePLBallPair_Icc hab
  obtain ⟨J, hJ, hJs, _⟩ := I.exists_finite_triangulation_prod A hI hA
  exact ⟨J, hJ, hJs.trans (congrArg (fun s => s ×ˢ A.space) hIs)⟩

private theorem collar_band_polyhedralPL
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V} {K : Set E} {c : E × ℝ → X} {a : ℝ}
    (hc : PolyhedralPLInCharts e c (K ×ˢ Icc (0 : ℝ) a))
    (A : SimplicialComplex ℝ Z) (rim : Z → E)
    (hrim : FinitePiecewiseAffineOn rim A.space) (hrimK : MapsTo rim A.space K)
    (J : SimplicialComplex ℝ (ℝ × Z)) (hJ : J.faces.Finite)
    (hJA : MapsTo Prod.snd J.space A.space) (h : (ℝ × Z) →ᴬ[ℝ] ℝ)
    (hh : MapsTo h J.space (Icc (0 : ℝ) a)) :
    PolyhedralPLInCharts e (fun z => c (rim z.2, h z)) J.space := by
  let snd := (ContinuousLinearMap.snd ℝ ℝ Z).toContinuousAffineMap
  have hr : FinitePiecewiseAffineOn (fun z : ℝ × Z => rim z.2) J.space :=
    hrim.comp ((J.affineOnFaces_affine snd).finitePiecewiseAffineOn hJ) hJA
  exact hc.comp_finitePiecewiseAffineOn J hJ
    (hr.prod_mk ((J.affineOnFaces_affine h).finitePiecewiseAffineOn hJ))
    (fun z hz => ⟨hrimK (hJA hz), hh hz⟩)

theorem polyhedralPLInCharts_commonCollarAttachment
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (c : E × ℝ → X) (rim : Bool → Z → E)
    {K : Set E} (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    {a : ℝ} (ha : 0 < a)
    (hc : PolyhedralPLInCharts e c (K ×ˢ Icc (0 : ℝ) a))
    (hrim : ∀ b, FinitePiecewiseAffineOn (rim b) A.space)
    (hrimK : ∀ b, MapsTo (rim b) A.space K)
    (G : X → X) (f : ℝ × Z → X)
    (hmid : PolyhedralPLInCharts e (G ∘ f) (Icc (-1 : ℝ) 1 ×ˢ A.space))
    (hbase : ∀ b z, z ∈ A.space → c (rim b z, 0) = f (if b then 1 else -1, z))
    (hlevel : ∀ b z, z ∈ A.space → G (c (rim b z, 0)) = c (rim b z, a)) :
    PolyhedralPLInCharts e (commonCollarAttachment c rim G f a)
      (Icc (-2 : ℝ) 2 ×ˢ A.space) := by
  obtain ⟨L, hL, hLs⟩ := exists_finite_interval_cylinder A hA (show (-2 : ℝ) < -1 by norm_num)
  obtain ⟨M, hM, hMs⟩ := exists_finite_interval_cylinder A hA (show (-1 : ℝ) < 1 by norm_num)
  obtain ⟨U, hU, hUs⟩ := exists_finite_interval_cylinder A hA (show (1 : ℝ) < 2 by norm_num)
  let fst := (ContinuousLinearMap.fst ℝ ℝ Z).toContinuousAffineMap
  let lower : (ℝ × Z) →ᴬ[ℝ] ℝ := a • (fst + ContinuousAffineMap.const ℝ (ℝ × Z) 2)
  let upper : (ℝ × Z) →ᴬ[ℝ] ℝ := a • (ContinuousAffineMap.const ℝ (ℝ × Z) 2 - fst)
  have hlPL := collar_band_polyhedralPL hc A (rim false) (hrim false) (hrimK false)
    L hL (fun _ hz => (hLs.subset hz).2) lower (by
      intro z hz
      change 0 ≤ a * (z.1 + 2) ∧ a * (z.1 + 2) ≤ a
      have ht := (hLs.subset hz).1
      constructor <;> nlinarith [ht.1, ht.2])
  have huPL := collar_band_polyhedralPL hc A (rim true) (hrim true) (hrimK true)
    U hU (fun _ hz => (hUs.subset hz).2) upper (by
      intro z hz
      change 0 ≤ a * (2 - z.1) ∧ a * (2 - z.1) ≤ a
      have ht := (hUs.subset hz).1
      constructor <;> nlinarith [ht.1, ht.2])
  have hLPL : PolyhedralPLInCharts e (commonCollarAttachment c rim G f a) L.space := by
    apply hlPL.congr
    intro z hz
    exact (if_pos (hLs.subset hz).1.2).symm
  have hMPL : PolyhedralPLInCharts e (commonCollarAttachment c rim G f a) M.space := by
    apply (hMs.symm ▸ hmid).congr
    intro z hz
    exact (commonCollarAttachment_middle c rim G f a hbase hlevel (hMs.subset hz)).symm
  have hUPL : PolyhedralPLInCharts e (commonCollarAttachment c rim G f a) U.space := by
    apply huPL.congr
    intro z hz
    have ht := (hUs.subset hz).1
    simp only [commonCollarAttachment, if_neg (show ¬z.1 ≤ -1 by linarith [ht.1]),
      if_pos ht.1]
    rfl
  obtain ⟨LM, hLM, hLMs⟩ := L.exists_finite_triangulation_union M hL hM
  have hLMPL : PolyhedralPLInCharts e (commonCollarAttachment c rim G f a) LM.space :=
    hLMs.symm ▸ PolyhedralPLInCharts.union_of_finite hcompat L M hL hM hLPL hMPL
  have hall := PolyhedralPLInCharts.union_of_finite hcompat LM U hLM hU hLMPL hUPL
  have hcover : LM.space ∪ U.space = Icc (-2 : ℝ) 2 ×ˢ A.space := by
    rw [hLMs, hLs, hMs, hUs]
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩
      · exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
      · exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, hz.2⟩
    · intro hz
      by_cases hl : z.1 ≤ -1
      · exact Or.inl (Or.inl ⟨⟨hz.1.1, hl⟩, hz.2⟩)
      · by_cases hu : 1 ≤ z.1
        · exact Or.inr ⟨⟨hu, hz.1.2⟩, hz.2⟩
        · exact Or.inl (Or.inr ⟨⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩, hz.2⟩)
  exact hcover ▸ hall

end PoincareConjecture.M76
