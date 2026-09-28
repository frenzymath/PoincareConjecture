import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.Standard
import PoincareConjecture.Proofs.M76.Rigidity.MeridianBandCarrier
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL








set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L


noncomputable def standardMeridianBandAffineLift (a b : ℝ) :
    (V2 × ℝ) →ᴬ[ℝ] ((Fin 1 ⊕ Fin 2) → ℝ) :=
  (ContinuousLinearMap.pi fun i : Fin 1 ⊕ Fin 2 => (match i with
    | Sum.inl _ => (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ V2 ℝ)
    | Sum.inr j => if j = 0 then ContinuousLinearMap.snd ℝ V2 ℝ else
        ((b - a) / 2) •
          ((ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ V2 ℝ)) :
      (V2 × ℝ) →L[ℝ] ℝ)).toContinuousAffineMap +
    ContinuousAffineMap.const ℝ (V2 × ℝ)
      (Sum.elim (fun _ => 0) ![0, (b - a) / 2 + a])

theorem standardMeridianBandAffineLift_projection (a b : ℝ) (z : V2 × ℝ) :
    latticeCoordinateProjection (Fin 1) (Fin 2) L
      (standardMeridianBandAffineLift a b z) = standardMeridianBandParameter a b z := by
  apply Prod.ext
  · funext i
    simp [latticeCoordinateProjection, standardMeridianBandAffineLift,
      standardMeridianBandParameter]
  · apply congrArg QuotientAddGroup.mk
    funext i
    fin_cases i
    · simp [standardMeridianBandAffineLift]
    · simp [standardMeridianBandAffineLift]
      ring



theorem polyhedralPL_standardMeridianBandParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (a b : ℝ) :
    PolyhedralPLInCharts d (standardMeridianBandParameter a b)
      (Q ×ˢ Icc (-1 : ℝ) 1) := by
  obtain ⟨K, hK, hKS⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  have hv : FinitePiecewiseAffineOn (standardMeridianBandAffineLift a b)
      (Q ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine (standardMeridianBandAffineLift a b)⟩
  exact (hd.polyhedralPL_projection hv).congr
    (fun z _ => standardMeridianBandAffineLift_projection a b z)

end PoincareConjecture.M76.HamiltonIntervalTorus
