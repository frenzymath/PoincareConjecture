import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.CylinderFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift








set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareConjecture.M76

open Dehn Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

private theorem interval_one_bounds (v : V1) :
    v ∈ closedBall (0 : V1) 1 ↔ -1 ≤ v 0 ∧ v 0 ≤ 1 := by
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv, mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs, abs_le]

private theorem interval_one_rim (v : V1) :
    v ∈ sphere (0 : V1) 1 ↔ v 0 = -1 ∨ v 0 = 1 := by
  have hv : v = fun _ => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv, mem_sphere_zero_iff_norm, pi_norm_const, Real.norm_eq_abs]
  exact (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).trans or_comm

theorem PLDomain.exists_original_common_collared_annulus_family
    {X ι T : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (f : T → V1 × V2 → X)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) source)
    (hfi : ∀ i, InjOn (f i) source)
    (hfR : ∀ i, MapsTo (f i) source R)
    (hfB : ∀ i (b : Bool) z, z ∈ Q → f i (endpoint b, z) ∈ frontier R) :
    ∃ (s : Finset R) (K : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : K.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X)
      (a : ℝ) (rim : T → Bool → V2 → (s → ℝ × V3)) (g : T → V1 × V2 → X),
      K.faces.Finite ∧ 0 < a ∧ a < 1 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) 1) ∧
      IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) 1) => c z) ∧
      MapsTo c (K.space ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ z : K.space, c (z, 0) = HB z) ∧
      (∀ z ∈ K.space ×ˢ Icc (0 : ℝ) 1, c z ∈ frontier R ↔ z.2 = 0) ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) a))) ∧
      ∀ i,
        (∀ b, FinitePiecewiseAffineOn (rim i b) Q) ∧
        (∀ b, MapsTo (rim i b) Q K.space) ∧
        (∀ b z, z ∈ Q → c (rim i b z, 0) = f i (endpoint b, z)) ∧
        PolyhedralPLInCharts e (g i) source ∧ InjOn (g i) source ∧ MapsTo (g i) source R ∧
        (∀ z ∈ source, g i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1) ∧
        (∀ b z, z ∈ Q → g i (endpoint b, z) = f i (endpoint b, z)) ∧
        (g i '' source) ∩ (c '' (K.space ×ˢ Ico (0 : ℝ) a)) =
          c '' (((rim i false '' Q) ∪ (rim i true '' Q)) ×ˢ Ico (0 : ℝ) a) := by
  let A := squareRimPolygon.simplicialComplex hasSimplicialEdges_squareRimPolygon
  have hA : A.faces.Finite :=
    squareRimPolygon.finite_simplicialComplex_faces hasSimplicialEdges_squareRimPolygon
  have hAs : A.space = Q :=
    (squareRimPolygon.simplicialComplex_space hasSimplicialEdges_squareRimPolygon).trans
      boundary_squareRimPolygon
  let p : (ℝ × V2) →L[ℝ] (V1 × V2) :=
    (ContinuousLinearMap.pi (fun _ : Fin 1 => ContinuousLinearMap.fst ℝ ℝ V2)).prod
      (ContinuousLinearMap.snd ℝ ℝ V2)
  have hpval (z : ℝ × V2) : p z = ((fun _ => z.1), z.2) := rfl
  have hpmap : MapsTo p (Icc (-1 : ℝ) 1 ×ˢ A.space) source := by
    intro z hz
    exact ⟨(interval_one_bounds _).mpr hz.1, hAs.subset hz.2⟩
  have hpi : Function.Injective p := by
    intro x y h
    exact Prod.ext (congrArg (fun z : V1 × V2 => z.1 0) h)
      (congrArg (fun z : V1 × V2 => z.2) h)
  obtain ⟨M, hM, hMs⟩ := exists_finite_interval_cylinder A hA (show (-1 : ℝ) < 1 by norm_num)
  have hfp : ∀ i, PolyhedralPLInCharts e (f i ∘ p) (Icc (-1 : ℝ) 1 ×ˢ A.space) := by
    intro i
    rw [← hMs]
    exact (hf i).comp_finitePiecewiseAffineOn M hM
      ((M.affineOnFaces_affine p.toContinuousAffineMap).finitePiecewiseAffineOn hM)
      (fun _ hz => hpmap (hMs.subset hz))
  have hpend (b : Bool) (z : V2) : p (if b then 1 else -1, z) = (endpoint b, z) := by
    cases b <;> rfl
  obtain ⟨s, K, HB, c, a, rim, g, hK, ha, ha1, hc, hci, hcm, hcb, hcp, hco, hg⟩ :=
    he.exists_original_common_collared_cylinder_family hR hconn A hA (fun i => f i ∘ p)
      hfp (fun i => (hfi i).comp hpi.injOn hpmap)
      (fun i => (hfR i).comp hpmap) (fun i b z hz => by
        change f i (p _) ∈ frontier R
        rw [hpend]
        exact hfB i b z (hAs.subset hz))
  let ev : V1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let q : (V1 × V2) →L[ℝ] (ℝ × V2) :=
    ((2 : ℝ) • (ev.comp (ContinuousLinearMap.fst ℝ V1 V2))).prod
      (ContinuousLinearMap.snd ℝ V1 V2)
  have hqval (z : V1 × V2) : q z = (2 * z.1 0, z.2) := rfl
  have hqmap : MapsTo q source (Icc (-2 : ℝ) 2 ×ˢ A.space) := by
    intro z hz
    have ht := (interval_one_bounds _).mp hz.1
    exact ⟨⟨by change -2 ≤ 2 * z.1 0; linarith [ht.1],
      by change 2 * z.1 0 ≤ 2; linarith [ht.2]⟩, hAs.symm.subset hz.2⟩
  have hqi : Function.Injective q := by
    intro x y h
    have ht := congrArg Prod.fst h
    refine Prod.ext ?_ (congrArg (fun z : ℝ × V2 => z.2) h)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change 2 * x.1 0 = 2 * y.1 0 at ht
    linarith
  have hqsurj : q '' source = Icc (-2 : ℝ) 2 ×ˢ A.space := by
    apply Subset.antisymm (image_subset_iff.mpr hqmap)
    intro z hz
    refine ⟨((fun _ : Fin 1 => z.1 / 2), z.2), ?_, ?_⟩
    · exact ⟨(interval_one_bounds _).mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        hAs.subset hz.2⟩
    · change (2 * (z.1 / 2), z.2) = z
      exact Prod.ext (by ring) rfl
  obtain ⟨D, hD, hDs⟩ := exists_source_triangulation
  refine ⟨s, K, HB, c, a, rim, fun i => g i ∘ q, hK, ha, ha1, hc, hci, hcm, hcb, hcp, hco, ?_⟩
  intro i
  obtain ⟨hrim, hrimK, hrimb, hgPL, hgi, hgR, hgp, hge, hgt⟩ := hg i
  refine ⟨fun b => hAs ▸ hrim b, fun b => hAs ▸ hrimK b, ?_, ?_,
    hgi.comp hqi.injOn hqmap, hgR.comp hqmap, ?_, ?_, ?_⟩
  · intro b z hz
    simpa only [Function.comp_apply, hpend] using hrimb b z (hAs.symm.subset hz)
  · rw [← hDs]
    exact hgPL.comp_finitePiecewiseAffineOn D hD
      ((D.affineOnFaces_affine q.toContinuousAffineMap).finitePiecewiseAffineOn hD)
      (fun _ hz => hqmap (hDs.subset hz))
  · intro z hz
    change g i (q z) ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1
    rw [hgp _ (hqmap hz), interval_one_rim]
    change (2 * z.1 0 = -2 ∨ 2 * z.1 0 = 2) ↔ z.1 0 = -1 ∨ z.1 0 = 1
    constructor <;> rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · intro b z hz
    have hqe : q (endpoint b, z) = (if b then 2 else -2, z) := by
      cases b <;> ext <;> norm_num [q, ev, endpoint]
    simpa only [Function.comp_apply, hqe, hpend] using hge b z (hAs.symm.subset hz)
  · rw [image_comp, hqsurj]
    simpa only [hAs] using hgt

end PoincareConjecture.M76
