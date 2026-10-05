import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceDiskState
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.FiniteAmbientFamilies
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.WhiskeredHomotopyClass
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.SquareRimLoop

/-!
# The literal original marked homotopy of the finite face history

Compose the particular ambient families retained in the actual finite
history. Their endpoint equals the last whole source map. The original
projection of the same family gives a homotopy in the whole mark and
the literal basepoint trace retaining the same excluded class.
See Hatcher pp.45--46 and Dehn032 finite-assembly supplement, section5.
-/

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareMT.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Qrim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

/-- The actual finite history supplies a jointly continuous ambient
family with its literal final map and full marked rim homotopy.
Appending its actual basepoint trace preserves exclusion from the
unchanged original subgroup. No position or descent conclusion is
inferred here. See Dehn032 finite-assembly supplement, section5. -/
theorem Step.exists_original_face_history_homotopy
    {s t : Stage e S f r C} (step : Step s t)
    {K : SimplicialComplex ℝ V2} (hKD : K.space = D)
    {n : ℕ} {P : ℕ → SimplicialComplex ℝ V2}
    {boundary : Fin n → Bool}
    {Q : Fin n → OpenPartialHomeomorph t.Carrier V3}
    {B : Fin n → OpenPartialHomeomorph s.Carrier V3}
    {support : Fin n → SimplicialComplex ℝ V3}
    {U : K.faces → Set t.Carrier} {R Fmark : Set M}
    (states : ℕ → FaceDiskState t K U R Fmark)
    (hsteps : ∀ i (hi : i < n),
      ∃ motion : FaceMotionData step K (P i) (P (i + 1)) (states i).map
        (Q ⟨i, hi⟩) (B ⟨i, hi⟩) (support ⟨i, hi⟩) U R Fmark (boundary ⟨i, hi⟩),
        (states (i + 1)).map = motion.ambient 1 ∘ (states i).map)
    (rim : C(Qrim, Fmark))
    (hrim : ∀ x : Qrim, t.projection ((states 0).map x) = (rim x : M))
    {base : Fmark} (q : Path base (rim squareRimBase))
    (J : Subgroup (FundamentalGroup Fmark base))
    (hout : q.whiskeredLoopClass (squareRimLoop.map rim.continuous) ∉ J) :
    ∃ (G : I → t.Carrier ≃ₜ t.Carrier) (rim' : C(Qrim, Fmark))
      (eta : rim.Homotopy rim'),
      Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
      Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
      (∀ x, G 0 x = x) ∧
      (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
        (G a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
      (states n).map = G 1 ∘ (states 0).map ∧
      (∀ a x, (eta (a, x) : M) = t.projection (G a ((states 0).map x))) ∧
      (∀ x : Qrim, t.projection ((states n).map x) = (rim' x : M)) ∧
      (q.trans (eta.evalAt squareRimBase)).whiskeredLoopClass
        (squareRimLoop.map rim'.continuous) ∉ J := by
  classical
  choose motion htransition using fun i : Fin n => hsteps i.val i.isLt
  obtain ⟨G, hG, hGi, hzero, hsets, hfinal⟩ :=
    Homeomorph.exists_finite_family_history_composite
      (fun i => (motion i).ambient) (fun i => (motion i).continuous_ambient)
      (fun i => (motion i).continuous_inverse) (fun i => (motion i).zero)
      (fun i => (motion i).region) (fun i => (motion i).mark)
      (fun k => (states k).map) (fun i hi => htransition ⟨i, hi⟩)
  have hcontinuous (k : ℕ) : Continuous (fun x : Qrim => (states k).map x) :=
    (states k).original_PL.continuousOn.comp_continuous continuous_subtype_val
      (fun x => hKD.symm.subset (sphere_subset_closedBall x.property))
  have hmark (a : I) (x : Qrim) :
      t.projection (G a ((states 0).map x)) ∈ Fmark := by
    change (states 0).map x ∈ (G a) ⁻¹' (t.projection ⁻¹' Fmark)
    rw [(hsets a).2]
    exact (states 0).mark x.property
  let rim' : C(Qrim, Fmark) :=
    ⟨fun x => ⟨t.projection ((states n).map x), (states n).mark x.property⟩,
      (t.projection.continuous.comp (hcontinuous n)).subtype_mk _⟩
  let eta : rim.Homotopy rim' :=
    { toFun := fun z => ⟨t.projection (G z.1 ((states 0).map z.2)), hmark z.1 z.2⟩
      continuous_toFun := (t.projection.continuous.comp
        (hG.comp (continuous_fst.prodMk ((hcontinuous 0).comp continuous_snd)))).subtype_mk _
      map_zero_left := by
        intro x
        apply Subtype.ext
        change t.projection (G 0 ((states 0).map x)) = (rim x : M)
        rw [hzero, hrim x]
      map_one_left := by
        intro x
        apply Subtype.ext
        change t.projection (G 1 ((states 0).map x)) = t.projection ((states n).map x)
        rw [hfinal]
        rfl }
  refine ⟨G, rim', eta, hG, hGi, hzero, hsets, hfinal,
    fun _ _ => rfl, fun _ => rfl, ?_⟩
  rw [← eta.whiskeredLoopClass_eq q squareRimLoop]
  exact hout

end Geometry.OriginalPLTower
