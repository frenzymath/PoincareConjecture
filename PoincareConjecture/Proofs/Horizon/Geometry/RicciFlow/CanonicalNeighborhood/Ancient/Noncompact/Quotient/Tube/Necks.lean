import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Neck.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Bounds.Curvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  (C : M27TwistedSphereLineFlowCertificate K)
  {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hhalf : epsilon < 1 / 2)
  (q : UnitTwoSphere)
  (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
  (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
    (K.flow.connection t).scalarCurvature (C.cover (q, 0)) *
      (C.sphere.metric t).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
  (s : ℝ)
  (hs : epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) ≤ s)

noncomputable def neckAtHeight : StrongEvolvingNeck K t epsilon :=
  C.strongNeck ht hε hhalf (q, s) (C.scalarCurvature_pos ht _) a
    (by rw [C.scalarCurvature_eq ht (C.cover (q, s)) (C.cover (q, 0))]; exact ha)
    (by rw [C.scalarCurvature_eq ht (C.cover (q, s)) (C.cover (q, 0))]; exact hs)

@[simp] theorem neckAtHeight_center :
    (C.neckAtHeight ht hε hhalf q a ha s hs).center = C.cover (q, s) := rfl

@[simp] theorem neckAtHeight_terminal_center :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.center = C.cover (q, s) := rfl

@[simp] theorem neckAtHeight_epsilon :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.epsilon = epsilon := rfl

theorem neckAtHeight_scale :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.scale =
      ((K.flow.connection t).scalarCurvature (C.cover (q, 0))) ^ (-1 / 2 : ℝ) := by
  change ((K.flow.connection t).scalarCurvature (C.cover (q, s))) ^ (-1 / 2 : ℝ) = _
  rw [C.scalarCurvature_eq ht (C.cover (q, s)) (C.cover (q, 0))]

theorem neckAtHeight_carrier :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.carrier =
      C.cover '' (univ ×ˢ Ioo
        (s - epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))
        (s + epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))) := by
  unfold neckAtHeight
  rw [C.strongNeck_carrier, C.scalarCurvature_eq ht (C.cover (q, s)) (C.cover (q, 0))]

theorem neckAtHeight_central_sphere :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.central_sphere =
      C.cover '' (univ ×ˢ ({s} : Set ℝ)) := by
  unfold neckAtHeight
  exact C.strongNeck_central_sphere _ _ _ _ _ _ _ _

theorem neckAtHeight_region {l u : ℝ} (hl : -epsilon⁻¹ ≤ l) (hu : u ≤ epsilon⁻¹) :
    (C.neckAtHeight ht hε hhalf q a ha s hs).terminal_neck.region l u =
      C.cover '' (univ ×ˢ Ioo
        (s + l / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))
        (s + u / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0))))) := by
  unfold neckAtHeight
  rw [C.strongNeck_region _ _ _ _ _ _ _ _ hl hu,
    C.scalarCurvature_eq ht (C.cover (q, s)) (C.cover (q, 0))]

noncomputable def neckSpacing : ℝ :=
  epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover (q, 0)))

include ht hε in
theorem neckSpacing_pos : 0 < C.neckSpacing (t := t) (epsilon := epsilon) q :=
  div_pos (inv_pos.mpr hε) (Real.sqrt_pos.mpr (C.scalarCurvature_pos ht _))

noncomputable def endNeck (i : ℤ) : StrongEvolvingNeck K t epsilon :=
  C.neckAtHeight ht hε hhalf q a ha
    ((max (i : ℝ) 0 + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q)
    (by
      change C.neckSpacing (t := t) (epsilon := epsilon) q ≤ _
      have hL := C.neckSpacing_pos ht hε q
      have hi := le_max_right (i : ℝ) 0
      nlinarith)

theorem endNeck_center (i : ℤ) (hi : 0 ≤ i) :
    (C.endNeck ht hε hhalf q a ha i).terminal_neck.center =
      C.cover (q, ((i : ℝ) + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q) := by
  change C.cover (q, (max (i : ℝ) 0 + 2) * _) = _
  rw [max_eq_left (by exact_mod_cast hi : (0 : ℝ) ≤ i)]

theorem endNeck_carrier (i : ℤ) (hi : 0 ≤ i) :
    (C.endNeck ht hε hhalf q a ha i).terminal_neck.carrier =
      C.cover '' (univ ×ˢ Ioo
        (((i : ℝ) + 1) * C.neckSpacing (t := t) (epsilon := epsilon) q)
        (((i : ℝ) + 3) * C.neckSpacing (t := t) (epsilon := epsilon) q)) := by
  unfold endNeck
  rw [C.neckAtHeight_carrier, max_eq_left (by exact_mod_cast hi : (0 : ℝ) ≤ i)]
  congr 3 <;> dsimp [neckSpacing] <;> ring

theorem endNeck_central_sphere (i : ℤ) (hi : 0 ≤ i) :
    (C.endNeck ht hε hhalf q a ha i).terminal_neck.central_sphere =
      C.cover '' (univ ×ˢ ({((i : ℝ) + 2) * C.neckSpacing (t := t) (epsilon := epsilon) q} : Set ℝ)) := by
  unfold endNeck
  rw [C.neckAtHeight_central_sphere, max_eq_left (by exact_mod_cast hi : (0 : ℝ) ≤ i)]

theorem endNeck_region (i : ℤ) (hi : 0 ≤ i) {b c : ℝ} (hb : -1 ≤ b) (hc : c ≤ 1) :
    (C.endNeck ht hε hhalf q a ha i).terminal_neck.region (b * epsilon⁻¹) (c * epsilon⁻¹) =
      C.cover '' (univ ×ˢ Ioo
        (((i : ℝ) + 2 + b) * C.neckSpacing (t := t) (epsilon := epsilon) q)
        (((i : ℝ) + 2 + c) * C.neckSpacing (t := t) (epsilon := epsilon) q)) := by
  unfold endNeck
  have hl : -epsilon⁻¹ ≤ b * epsilon⁻¹ := by nlinarith [inv_pos.mpr hε]
  have hu : c * epsilon⁻¹ ≤ epsilon⁻¹ := by nlinarith [inv_pos.mpr hε]
  rw [C.neckAtHeight_region _ _ _ _ _ _ _ _ hl hu,
    max_eq_left (by exact_mod_cast hi : (0 : ℝ) ≤ i)]
  congr 3 <;> dsimp [neckSpacing] <;> ring

theorem endNeck_scale_mul_epsilon_inv (i : ℤ) :
    (C.endNeck ht hε hhalf q a ha i).terminal_neck.scale * epsilon⁻¹ =
      C.neckSpacing (t := t) (epsilon := epsilon) q := by
  unfold endNeck
  rw [C.neckAtHeight_scale]
  have hR := C.scalarCurvature_pos ht (C.cover (q, 0))
  rw [neg_div, Real.rpow_neg hR.le]
  dsimp [neckSpacing]
  rw [Real.sqrt_eq_rpow]
  ring

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
