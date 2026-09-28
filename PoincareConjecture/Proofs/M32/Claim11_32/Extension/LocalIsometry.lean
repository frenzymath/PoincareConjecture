import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32



theorem negativeCurvaturePart_eq_of_local_isometry
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
    [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]
    {g : RiemannianMetric 3 X} {g' : RiemannianMetric 3 Y}
    (D : LeviCivitaData g) (D' : LeviCivitaData g')
    {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hmetric : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = g'.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w))
    {x : X} (hx : x ∈ U) :
    D.negativeCurvaturePart x = D'.negativeCurvaturePart (f x) := by
  have hbij := g.mfderiv_bijective_of_pullback_eq g' x
    (fun v w => (hmetric x hx v w).symm)
  have horth (v w : TangentSpace (𝓡 3) x) :
      LeviCivitaData.IsOrthonormalPair g' (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) ↔
      LeviCivitaData.IsOrthonormalPair g x v w := by
    simp only [LeviCivitaData.IsOrthonormalPair, ← hmetric x hx]
  have hcurv := D.curvatureTensor_eq_of_local_isometry D' hU hf hmetric hx
  have hleast : D.leastSectionalCurvature x = D'.leastSectionalCurvature (f x) := by
    unfold LeviCivitaData.leastSectionalCurvature
    congr 1
    ext a
    constructor
    · rintro ⟨v, w, hvw, ha⟩
      exact ⟨_, _, (horth v w).mpr hvw, ha.trans (hcurv v w v w)⟩
    · rintro ⟨v, w, hvw, ha⟩
      obtain ⟨v', rfl⟩ := hbij.2 v
      obtain ⟨w', rfl⟩ := hbij.2 w
      exact ⟨v', w', (horth v' w').mp hvw, ha.trans (hcurv v' w' v' w').symm⟩
  simp only [LeviCivitaData.negativeCurvaturePart, hleast]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem extension_negativeCurvaturePart_pullback
    (E : GeneralizedFlowExtension F T) (t : ℝ) (ht : t ∈ F.interval)
    (x : (F.slice t).carrier) :
    (E.extended.connection t).negativeCurvaturePart (E.forward t ht x) =
      (F.connection t).negativeCurvaturePart x := by
  exact (negativeCurvaturePart_eq_of_local_isometry (F.connection t)
    (E.extended.connection t) isOpen_univ (E.forward_smooth t ht).contMDiffOn
    (fun y _ v w => (E.metric_pullback t ht y v w).symm) (mem_univ x)).symm



theorem extension_hamiltonIveyPinchedAt_old
    (H : SingularTimeAssumptions F T M) (E : GeneralizedFlowExtension F T)
    (t : ℝ) (ht : t ∈ F.interval) : generalizedHamiltonIveyPinchedAt E.extended t := by
  refine ⟨E.old_times ht, H.interval_nonnegative ht, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := (E.right_inverse t ht).surjective x
    change -6 / (1 + 4 * t) ≤ (E.extended.connection t).scalarCurvature _
    rw [E.scalar_pullback]
    have h := H.positive_pinching ⟨t, y⟩ ht
    change 0 ≤ (F.connection t).scalarCurvature y + 6 / (1 + 4 * t) at h
    rw [neg_div]
    linarith
  · intro x
    obtain ⟨y, rfl⟩ := (E.right_inverse t ht).surjective x
    change 0 < (E.extended.connection t).negativeCurvaturePart _ → _
    rw [extension_negativeCurvaturePart_pullback]
    change 0 < (F.connection t).negativeCurvaturePart y →
      _ ≤ (E.extended.connection t).scalarCurvature _
    rw [E.scalar_pullback]
    exact H.hamilton_ivey_pinching ⟨t, y⟩ ht

end PoincareConjecture.M32
