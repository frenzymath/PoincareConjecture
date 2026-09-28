import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteParameterVelocity





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]






theorem m64ParameterMotion_half_energy_hasDerivAt
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {Phi : ℝ × E → M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi O)
    {h : ℝ → E} {t x : ℝ} (hh : DifferentiableAt ℝ h x) (hp : (t, h x) ∈ O) :
    HasDerivAt
      (fun s => (1 / 2 : ℝ) * g.inner (Phi (s, h x))
        (curveVelocity (fun y => Phi (s, h y)) x)
        (curveVelocity (fun y => Phi (s, h y)) x))
      (g.inner (Phi (t, h x))
        (rampHorizontalCovariantDerivative D (fun y => Phi (t, h y))
          (fun y => curveVelocity (fun s => Phi (s, h y)) t) x)
        (curveVelocity (fun y => Phi (t, h y)) x)) t := by
  let H := fun y : ℝ => h x + (y - x) • deriv h x
  have hHx : H x = h x := by simp [H]
  have hH : HasDerivAt H (deriv h x) x := by
    simpa only [H, id_eq, one_smul] using!
      (((hasDerivAt_id x).sub_const x).smul_const (deriv h x)).const_add (h x)
  have hHs : ContDiff ℝ ∞ H := by dsimp only [H]; fun_prop
  let j := fun q : ℝ × ℝ => (q.1, H q.2)
  have hj : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × E) ∞ j :=
    (contDiff_fst.prodMk (hHs.comp contDiff_snd)).contMDiff
  have hW : IsOpen (j ⁻¹' O) := hO.preimage hj.continuous
  have hproxy : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun q : ℝ × ℝ => Phi (q.1, H q.2)) (j ⁻¹' O) :=
    hPhi.comp hj.contMDiffOn (fun _ hq => hq)
  have htx : (t, x) ∈ j ⁻¹' O := by simpa only [mem_preimage, j, hHx] using hp
  have hvel (s : ℝ) (hs : (s, h x) ∈ O) :
      curveVelocity (n := n) (fun y => Phi (s, H y)) x =
        curveVelocity (fun y => Phi (s, h y)) x := by
    have hsreg := (hPhi.contMDiffAt (hO.mem_nhds hs)).mdifferentiableAt (by simp)
    rw [m64ParameterMotion_spatial_velocity (hHx.symm ▸ hsreg) hH.differentiableAt,
      m64ParameterMotion_spatial_velocity hsreg hh, hHx, hH.deriv]
  have hpoint := hPhi.contMDiffAt (hO.mem_nhds hp)
  have hslice : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × E) ∞
      (fun q : E => (t, q)) (h x) := (contDiffAt_const.prodMk contDiffAt_id).contMDiffAt
  have hV := (m64ParameterMotion_timeVelocity_contMDiffAt hO hPhi hp).comp (h x) hslice
  have hjet := m64Pullback_covariantDerivative_eq_affine_parameter D hh
    (f := fun q => Phi (t, q)) (Y := fun q => curveVelocity (fun s => Phi (s, q)) t)
    ((hpoint.comp (h x) hslice).mdifferentiableAt (by simp))
    (hV.mdifferentiableAt (by simp))
  have henergy := m64MovingCurve_half_energy_hasDerivAt D
    (c := fun s y => Phi (s, H y)) hW hproxy htx
  have heq : (fun s => (1 / 2 : ℝ) * g.inner (Phi (s, h x))
      (curveVelocity (fun y => Phi (s, h y)) x)
      (curveVelocity (fun y => Phi (s, h y)) x)) =ᶠ[𝓝 t]
      (fun s => (1 / 2 : ℝ) * g.inner (Phi (s, H x))
        (curveVelocity (fun y => Phi (s, H y)) x)
        (curveVelocity (fun y => Phi (s, H y)) x)) := by
    filter_upwards [(continuous_id.prodMk continuous_const).continuousAt
      (hO.mem_nhds hp)] with s hs
    rw [hHx, hvel s hs]
  apply (henergy.congr_of_eventuallyEq heq).congr_deriv
  have hdata :
      (Phi (t, H x),
      (rampHorizontalCovariantDerivative D (fun y => Phi (t, H y))
        (fun y => curveVelocity (fun s => Phi (s, H y)) t) x : EuclideanSpace ℝ (Fin n)),
      (curveVelocity (fun y => Phi (t, H y)) x : EuclideanSpace ℝ (Fin n))) =
      (Phi (t, h x),
      (rampHorizontalCovariantDerivative D (fun y => Phi (t, h y))
        (fun y => curveVelocity (fun s => Phi (s, h y)) t) x : EuclideanSpace ℝ (Fin n)),
      (curveVelocity (fun y => Phi (t, h y)) x : EuclideanSpace ℝ (Fin n))) :=
    Prod.ext (congrArg (fun q => Phi (t, q)) hHx) (Prod.ext hjet.symm (hvel t hp))
  exact congrArg (fun q : M × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    g.inner q.1 q.2.1 q.2.2) hdata






theorem m64ParameterMotion_energy_derivative_eq_divergence
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {Phi : ℝ × E → M} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hPhi : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ Phi O)
    {h : ℝ → E} {t x : ℝ} (hh : DifferentiableAt ℝ h x) (hp : (t, h x) ∈ O)
    (hX : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) (fun y =>
      (⟨Phi (t, h y), curveVelocity (fun z => Phi (t, h z)) y⟩ :
        TangentBundle (𝓡 n) M)) x) :
    deriv (fun s => (1 / 2 : ℝ) * g.inner (Phi (s, h x))
        (curveVelocity (fun y => Phi (s, h y)) x)
        (curveVelocity (fun y => Phi (s, h y)) x)) t =
      deriv (fun y => g.inner (Phi (t, h y))
        (curveVelocity (fun s => Phi (s, h y)) t)
        (curveVelocity (fun z => Phi (t, h z)) y)) x -
      g.inner (Phi (t, h x)) (curveVelocity (fun s => Phi (s, h x)) t)
        (rampHorizontalCovariantDerivative D (fun y => Phi (t, h y))
          (fun y => curveVelocity (fun z => Phi (t, h z)) y) x) := by
  have harg := (hasDerivAt_const x t).prodMk hh.hasDerivAt
  have hc := ((hPhi.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)).comp x
    harg.differentiableAt.mdifferentiableAt
  have hV := ((m64ParameterMotion_timeVelocity_contMDiffAt hO hPhi hp).mdifferentiableAt
    (by simp)).comp x harg.differentiableAt.mdifferentiableAt
  have hpair := M62.hasDerivAt_metric_pairing D
    (γ := fun y => Phi (t, h y))
    (Y := fun y => curveVelocity (fun s => Phi (s, h y)) t)
    (Z := fun y => curveVelocity (fun z => Phi (t, h z)) y) hc hV hX
  have henergy := m64ParameterMotion_half_energy_hasDerivAt D hO hPhi hh hp
  rw [henergy.deriv, hpair.deriv]
  ring

end PoincareConjecture
