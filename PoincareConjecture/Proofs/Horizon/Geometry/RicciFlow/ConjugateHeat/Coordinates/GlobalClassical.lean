import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.GlobalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Classical
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Density

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem heat_equation_of_contMDiffOn_weakPairing_eq_zero
    (F : RicciFlow n M (Iio (0 : ℝ))) {u : M × ℝ → ℝ}
    (hu : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ u (univ ×ˢ Ioi (0 : ℝ)))
    (hweak : ∀ φ : M × ℝ → ℝ,
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ univ ×ˢ Ioi (0 : ℝ) → weakPairing F u φ = 0)
    (x : M) {τ : ℝ} (hτ : 0 < τ) :
    deriv (fun t => u (x, t)) τ -
      (F.connection (-τ)).laplacian (fun y => u (y, τ)) x +
      (F.connection (-τ)).scalarCurvature x * u (x, τ) = 0 := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  let D := e.source ×ˢ Ioi (0 : ℝ)
  let v : Spacetime n → ℝ := fun z => u (e z.1, z.2)
  have hD : IsOpen D := e.open_source.prod isOpen_Ioi
  have hUD : D ⊆ BackwardCoordinates.domain (Iio (0 : ℝ)) e := by
    rw [BackwardCoordinates.domain_Iio_zero]
  have hv : ContDiffOn ℝ ∞ v D := by
    intro z hz
    have hmap : ContMDiffAt 𝓘(ℝ, Spacetime n) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun y : Spacetime n => (e y.1, y.2)) z :=
      ((he.contMDiffAt (e.open_source.mem_nhds hz.1)).comp z
        contDiffAt_fst.contMDiffAt).prodMk contDiffAt_snd.contMDiffAt
    exact (contMDiffAt_iff_contDiffAt.mp
      ((hu.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
        ⟨mem_univ _, hz.2⟩)).comp z hmap)).contDiffWithinAt
  have hp : x ∈ e.target := mem_chart_source _ x
  have hz : (e.symm x, τ) ∈ D := ⟨e.map_target hp, hτ⟩
  have hEq := BackwardCoordinates.heat_equation_of_smooth_weak_pairing F e he hei hD hUD hv
    (fun φ hφ hφc hφD =>
      coordinate_pairing_eq_zero_of_weakPairing_eq_zero F e he hei hu.continuousOn
        hweak hφ hφc hφD) hz
  have hd := (hv.contDiffAt (hD.mem_nhds hz)).differentiableAt (by simp)
  have ht := (hd.hasFDerivAt.comp_hasDerivAt τ
    ((hasDerivAt_const τ (e.symm x)).prodMk (hasDerivAt_id τ))).deriv
  have ht' : Canonical.timeDeriv v (e.symm x, τ) = deriv (fun t => u (x, t)) τ := by
    simpa only [Canonical.timeDeriv, v, Function.comp_def, e.right_inv hp] using ht.symm
  have hslice : (fun y => v (e.symm y, τ)) =ᶠ[𝓝 x] (fun y => u (y, τ)) := by
    filter_upwards [e.open_target.mem_nhds hp] with y hy
    simp only [v, e.right_inv hy]
  rw [ht', e.right_inv hp,
    (F.connection (-τ)).laplacian_eq_of_eventuallyEq hslice] at hEq
  simpa only [v, e.right_inv hp] using hEq

theorem normalizedDensity_contMDiffOn {l : M × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l
      (univ ×ˢ Ioi (0 : ℝ))) :
    ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) (univ ×ˢ Ioi (0 : ℝ)) := by
  intro z hz
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ => t ^ (-(n : ℝ) / 2)) z.2 :=
    contDiffAt_id.rpow_const_of_ne hz.2.ne'
  have hlz := hl.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds hz)
  have hexp := Real.contDiff_exp.contMDiff.contMDiffAt.comp z hlz.neg
  exact ((ht.contMDiffAt.comp z contMDiffAt_snd).mul hexp).contMDiffWithinAt

theorem potential_heat_equation_of_contMDiffOn_weakPairing_eq_zero
    (F : RicciFlow n M (Iio (0 : ℝ))) {l : M × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)))
    (hweak : ∀ φ : M × ℝ → ℝ,
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ univ ×ˢ Ioi (0 : ℝ) →
      weakPairing F (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ = 0)
    (x : M) {τ : ℝ} (hτ : 0 < τ) :
    deriv (fun t => l (x, t)) τ -
      (F.connection (-τ)).laplacian (fun y => l (y, τ)) x +
      (F.metric (-τ)).inner x
        ((F.connection (-τ)).gradient (fun y => l (y, τ)) x)
        ((F.connection (-τ)).gradient (fun y => l (y, τ)) x) -
      (F.connection (-τ)).scalarCurvature x + (n : ℝ) / (2 * τ) = 0 := by
  let v : M × ℝ → ℝ := fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)
  have hEq := heat_equation_of_contMDiffOn_weakPairing_eq_zero F
    (normalizedDensity_contMDiffOn hl) hweak x hτ
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => l (y, τ)) := by
    intro y
    have hly : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (y, τ) :=
      hl.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
        (show (y, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ y, hτ⟩))
    exact hly.comp y (contMDiffAt_id.prodMk contMDiffAt_const)
  have ht : DifferentiableAt ℝ (fun t => l (x, t)) τ := by
    have hlx : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (x, τ) :=
      hl.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
        (show (x, τ) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ x, hτ⟩))
    have hlt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t => l (x, t)) τ :=
      hlx.comp τ (contMDiffAt_const.prodMk contMDiffAt_id)
    exact (contMDiffAt_iff_contDiffAt.mp hlt).differentiableAt (by simp)
  have hp := (hasDerivAt_id τ).rpow_const (p := -(n : ℝ) / 2) (Or.inl hτ.ne')
  have hd : deriv (fun t => v (x, t)) τ =
      v (x, τ) * (-(n : ℝ) / (2 * τ) - deriv (fun t => l (x, t)) τ) := by
    have h := (hp.mul ht.hasDerivAt.neg.exp).deriv
    simp only [Pi.mul_apply, Pi.neg_apply, id_eq, one_mul] at h
    change deriv (fun t => t ^ (-(n : ℝ) / 2) * Real.exp (-l (x, t))) τ = _ at h
    change deriv (fun t => t ^ (-(n : ℝ) / 2) * Real.exp (-l (x, t))) τ = _
    rw [h]
    dsimp only [v]
    rw [Real.rpow_sub hτ, Real.rpow_one]
    field_simp
    ring
  have hL : (F.connection (-τ)).laplacian (fun y => v (y, τ)) x =
      v (x, τ) * ((F.metric (-τ)).inner x
        ((F.connection (-τ)).gradient (fun y => l (y, τ)) x)
        ((F.connection (-τ)).gradient (fun y => l (y, τ)) x) -
          (F.connection (-τ)).laplacian (fun y => l (y, τ)) x) := by
    dsimp only [v]
    rw [(F.connection (-τ)).laplacian_const_mul,
      (F.connection (-τ)).laplacian_exp_neg hs]
    ring
  change deriv (fun t => v (x, t)) τ -
    (F.connection (-τ)).laplacian (fun y => v (y, τ)) x +
    (F.connection (-τ)).scalarCurvature x * v (x, τ) = 0 at hEq
  rw [hd, hL] at hEq
  have hv : 0 < v (x, τ) := mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _)
  apply (mul_eq_zero.mp (show v (x, τ) *
      (deriv (fun t => l (x, t)) τ -
        (F.connection (-τ)).laplacian (fun y => l (y, τ)) x +
        (F.metric (-τ)).inner x
          ((F.connection (-τ)).gradient (fun y => l (y, τ)) x)
          ((F.connection (-τ)).gradient (fun y => l (y, τ)) x) -
        (F.connection (-τ)).scalarCurvature x + (n : ℝ) / (2 * τ)) = 0 by
      linear_combination -hEq)).resolve_left hv.ne'

end PoincareConjecture.RicciFlow.ConjugateHeat
