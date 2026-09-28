import PoincareConjecture.Statements.Ch06.LGeometry
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b τmax : ℝ}

noncomputable def backwardPathTail (p : BackwardTimePath F T 0 b)
    (ha : 0 < a) (hab : a < b) : BackwardTimePath F T a b where
  curve := p.curve
  nonnegative := ha.le
  ordered := hab
  terminal_mem := p.terminal_mem
  time_mem := fun s hs ↦ p.time_mem s ⟨ha.le.trans hs.1, hs.2⟩
  continuous := p.continuous.mono (Icc_subset_Icc ha.le le_rfl)
  regular := p.regular.mono (Ioo_subset_Ioo ha.le le_rfl)
  l_integrable := p.l_integrable.mono_set (by
    rw [uIcc_of_le hab.le, uIcc_of_le p.ordered.le]
    exact Icc_subset_Icc ha.le le_rfl)

omit [IsManifold (𝓡 n) ∞ M] in

theorem curveVelocityWithin_Ioo_eq {γ : ℝ → M} {c d s : ℝ} (hs : s ∈ Ioo c d) :
    curveVelocityWithin (n := n) γ (Ioo c d) s = curveVelocity γ s := by
  unfold curveVelocityWithin curveVelocity
  rw [mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)]

theorem isBackwardLGeodesic_tail {p : BackwardTimePath F T 0 b}
    (hp : IsBackwardLGeodesic F T 0 b p) (ha : 0 < a) (hab : a < b) :
    IsBackwardLGeodesic F T a b (backwardPathTail p ha hab) := by
  obtain ⟨E, hE⟩ := hp
  have hsub : Ioo a b ⊆ Ioo 0 b := Ioo_subset_Ioo ha.le le_rfl
  have hvel (s : ℝ) (hs : s ∈ Ioo a b) :
      curveVelocityWithin (n := n) p.curve (Ioo a b) s =
        curveVelocityWithin (n := n) p.curve (Ioo 0 b) s := by
    rw [curveVelocityWithin_Ioo_eq hs, curveVelocityWithin_Ioo_eq (hsub hs)]
  let E' : ParametricAlongCurveExtensionOn (Ioo a b) p.curve
      (curveVelocityWithin (n := n) p.curve (Ioo a b)) := {
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := fun s hs ↦ E.graph_mem s (hsub hs)
    smooth := E.smooth
    agrees := fun s hs ↦ (E.agrees s (hsub hs)).trans (hvel s hs).symm }
  refine ⟨E', ?_⟩
  intro s hs W
  have he := hE s (hsub hs) W
  change backwardEulerResidual F T p.curve (Ioo a b) E' s W = 0
  dsimp only [backwardEulerResidual, pullbackCovariantDerivative, E']
  rw [hvel s hs]
  exact he

variable [ConnectedSpace M]

theorem eulerPaths_eqOn_of_eventuallyEq (hL : LGeodesicTheory F T τmax)
    {p q : BackwardTimePath F T 0 b} (hmax : b ≤ τmax)
    (hp : IsBackwardLGeodesic F T 0 b p) (hq : IsBackwardLGeodesic F T 0 b q)
    (heq : p.curve =ᶠ[𝓝 b] q.curve) : EqOn p.curve q.curve (Icc 0 b) := by
  have hnear : {s : ℝ | p.curve s = q.curve s ∧ 0 < s} ∈ 𝓝 b :=
    heq.and (eventually_gt_nhds p.ordered)
  obtain ⟨a, hab, htail⟩ :=
    mem_nhdsLE_iff_exists_Icc_subset.mp (nhdsWithin_le_nhds hnear)
  have ha : 0 < a := (htail ⟨le_rfl, hab.le⟩).2
  obtain ⟨r, _, _, huniq⟩ := hL.extension_to_zero a b ha hab hmax
    (backwardPathTail p ha hab) (isBackwardLGeodesic_tail hp ha hab)
  have hp' := huniq p (fun _ _ ↦ rfl) hp
  have hq' := huniq q (fun s hs ↦ (htail hs).1.symm) hq
  exact fun s hs ↦ (hp' s hs).trans (hq' s hs).symm

end PoincareConjecture.M10
