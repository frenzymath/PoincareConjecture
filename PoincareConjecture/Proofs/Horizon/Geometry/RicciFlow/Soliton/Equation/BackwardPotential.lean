import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.EntropyEvolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_reverse_potential {l : M × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ))) :
    ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => l (z.1, -z.2)) (univ ×ˢ Iio (0 : ℝ)) :=
  hl.comp (contMDiffOn_fst.prodMk contMDiffOn_snd.neg)
    (fun z hz => ⟨mem_univ _, show 0 < -z.2 from neg_pos.mpr hz.2⟩)

theorem deriv_reverse_potential {l : M × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)))
    (x : M) {t : ℝ} (ht : t < 0) :
    deriv (fun s => l (x, -s)) t = -deriv (fun τ => l (x, τ)) (-t) := by
  have hpoint := hl.contMDiffAt ((isOpen_univ.prod isOpen_Ioi).mem_nhds
    (show (x, -t) ∈ univ ×ˢ Ioi (0 : ℝ) from ⟨mem_univ _, neg_pos.mpr ht⟩))
  have hd : DifferentiableAt ℝ (fun τ => l (x, τ)) (-t) :=
    (hpoint.comp (-t) (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt.differentiableAt
      (by simp)
  simpa [Function.comp_def] using (hd.hasDerivAt.comp t (hasDerivAt_neg t)).deriv

theorem soliton_equation_of_backward_scalar_equalities
    (F : RicciFlow n M (Iio (0 : ℝ))) {l : M × ℝ → ℝ}
    (hl : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)))
    (hheat : ∀ τ > 0, ∀ x,
      deriv (fun s => l (x, s)) τ - (F.connection (-τ)).laplacian (fun y => l (y, τ)) x +
        (F.metric (-τ)).inner x ((F.connection (-τ)).gradient (fun y => l (y, τ)) x)
          ((F.connection (-τ)).gradient (fun y => l (y, τ)) x) -
        (F.connection (-τ)).scalarCurvature x + (n : ℝ) / (2 * τ) = 0)
    (hhj : ∀ τ > 0, ∀ x,
      2 * deriv (fun s => l (x, s)) τ +
        (F.metric (-τ)).inner x ((F.connection (-τ)).gradient (fun y => l (y, τ)) x)
          ((F.connection (-τ)).gradient (fun y => l (y, τ)) x) -
        (F.connection (-τ)).scalarCurvature x + l (x, τ) / τ = 0) :
    ∀ t < 0, ∀ x : M, ∀ v w : TangentSpace (𝓡 n) x,
      (F.connection t).ricci x v w +
        (F.connection t).hessian (fun y => l (y, -t)) x v w +
        (1 / (2 * t)) * (F.metric t).inner x v w = 0 := by
  apply F.soliton_equation_of_scalar_equalities (contMDiffOn_reverse_potential hl)
  · intro t ht x
    have hh := hheat (-t) (neg_pos.mpr ht) x
    generalize hs : - -t = s at hh
    have hst : s = t := hs.symm.trans (neg_neg t)
    clear hs
    subst s
    simp only [potentialResidual, deriv_reverse_potential hl x ht]
    linarith
  · intro t ht x
    have hh := hheat (-t) (neg_pos.mpr ht) x
    have hj := hhj (-t) (neg_pos.mpr ht) x
    generalize hs : - -t = s at hh hj
    have hst : s = t := hs.symm.trans (neg_neg t)
    clear hs
    subst s
    change -t * (2 * (F.connection t).laplacian (fun y => l (y, -t)) x -
      (F.metric t).inner x ((F.connection t).gradient (fun y => l (y, -t)) x)
        ((F.connection t).gradient (fun y => l (y, -t)) x) +
      (F.connection t).scalarCurvature x) + l (x, -t) - n = 0
    field_simp [ne_of_lt ht] at hh hj
    nlinarith

end PoincareConjecture.RicciFlow
