import PoincareConjecture.Proofs.M09.VelocityRestriction
import PoincareConjecture.Proofs.M09.GeometricChartEquation
import PoincareConjecture.Proofs.M09.CoordinateEnergy
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

noncomputable def regularizedCurveEnergy {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (γ : ℝ → M) (s : ℝ) : ℝ :=
  (F.metric (T - s ^ 2)).inner (γ s) (curveVelocity γ s) (curveVelocity γ s)

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCurveEnergy_hasDerivAt {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U)
    (hI : UniqueDiffOn ℝ I) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ I) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (heq : regularizedLGeodesicEquation F T γ I E s) :
    HasDerivAt (regularizedCurveEnergy F T γ)
      (4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature
        (γ s) (curveVelocity γ s) -
        4 * s * (F.connection (T - s ^ 2)).ricci (γ s)
          (curveVelocity γ s) (curveVelocity γ s)) s := by
  let p := γ s
  let e := chartAt V p
  let S := U ∩ γ ⁻¹' e.source
  have hS : IsOpen S := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsS : s ∈ S := ⟨hIU hs, mem_chart_source V p⟩
  let a : ℝ → V := fun r ↦ e (γ r)
  let v : ℝ → V := deriv a
  have hgd : ∀ r ∈ U, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ r :=
    fun r hr ↦ (hγ.contMDiffAt (hU.mem_nhds hr)).mdifferentiableAt (by simp)
  have hasmooth : ContDiffOn ℝ ∞ a S := by
    have h : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ a S :=
      contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun r hr ↦ hr.2)
    exact h.contDiffOn
  have hvsmooth : ContDiffOn ℝ ∞ v S := hasmooth.deriv_of_isOpen hS (by simp)
  have had : ∀ r ∈ S, HasDerivAt a (v r) r :=
    fun r hr ↦ ((hasmooth.contDiffAt (hS.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  let K := I ∩ S
  have hKI : K ⊆ I := Set.inter_subset_left
  have hKS : K ⊆ S := Set.inter_subset_right
  have hK : UniqueDiffOn ℝ K := hI.inter hS
  have hsK : s ∈ K := ⟨hs, hsS⟩
  have hgdI : ∀ r ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ r :=
    fun r hr ↦ hgd r (hIU hr)
  let EK := restrictVelocityExtension γ I K hKI hI hK hgdI E
  have heK : regularizedLGeodesicEquation F T γ K EK s :=
    regularizedEquation_restrict F T γ I K hKI hI hK hgdI E s hsK heq
  have hvd : HasDerivAt v (deriv v s) s :=
    ((hvsmooth.contDiffAt (hS.mem_nhds hsS)).differentiableAt (by simp)).hasDerivAt
  have hw := (regularizedEquation_iff_coordinate_acceleration F hM04 T b hb hwindow
    p γ v S K hS hKS hK hvsmooth (fun r hr ↦ hgdI r hr.1)
    (fun r hr ↦ had r hr.2) (fun r hr ↦ hr.2.2) EK s hsK htime _ hvd).mp heK
  have hode : HasDerivAt v
      (regularizedCoordinatePhase (squareChartMetric F T p) (squareChartScalar F T p)
        (s, (a s, v s))).2 s := hvd.congr_deriv hw
  have hleft (r : ℝ) (hr : r ∈ S) : e.symm (a r) = γ r := e.left_inv hr.2
  have hvel (r : ℝ) (hr : r ∈ S) :
      (mfderiv (𝓡 n) (𝓡 n) e.symm (a r) (v r) : V) =
        (curveVelocity γ r : V) := by
    have hc := chartVectorField_at_inverse p (v r) (a r) (e.map_source hr.2)
    have hbase : (chartVectorField p (v r) (e.symm (a r)) : V) =
        (chartVectorField p (v r) (γ r) : V) :=
      congrArg (fun q ↦ (chartVectorField p (v r) q : V)) (hleft r hr)
    exact hc.symm.trans (hbase.trans
      (chartVectorField_coordinate_velocity p γ r (v r) hr.2 (hgd r hr.1) (had r hr)))
  have henergy : regularizedCurveEnergy F T γ =ᶠ[𝓝 s]
      (fun r ↦ squareChartMetric F T p (r, a r) (v r) (v r)) := by
    filter_upwards [hS.mem_nhds hsS] with r hr
    let Q : M → V → ℝ := fun q z ↦ (F.metric (T - r ^ 2)).inner q z z
    change Q (γ r) (curveVelocity γ r) = Q (e.symm (a r))
      (mfderiv (𝓡 n) (𝓡 n) e.symm (a r) (v r))
    exact (congrArg₂ Q (hleft r hr) (hvel r hr)).symm
  have hd := squareChartEnergy_hasDerivAt F hM04 T b hb hwindow p a v s htime
    (e.map_source hsS.2) (had s hsS) hode
  have hd' := hd.congr_of_eventuallyEq henergy
  apply hd'.congr_deriv
  let Q : M → V → ℝ := fun q z ↦
    4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature q z -
      4 * s * (F.connection (T - s ^ 2)).ricci q z z
  exact congrArg₂ Q (hleft s hsS) (hvel s hsS)

end PoincareConjecture.Proofs.M09
