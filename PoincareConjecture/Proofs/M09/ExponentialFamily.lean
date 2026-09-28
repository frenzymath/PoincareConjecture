import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Proofs.M09.NormalizedBackwardPath
import PoincareConjecture.Proofs.M09.ForwardSmoothFamily

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

local notation "V" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem nonempty_lExponentialFamily {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) (p : M) :
    Nonempty (LExponentialFamily F T τmax p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  let f : E × ℝ → M := fun z ↦ normalizedSquareFamily F T τmax p z.1 z.2
  have hex := fun (Z : E) (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) ↦
    exists_normalizedBackwardPath F hM04 T τmax hτmax hwindow hcurvature p Z b hb hbmax
  choose paths hpaths hregularizations using hex
  have hcontains : Set.univ ×ˢ Set.Ico 0 (Real.sqrt τmax) ⊆
      smoothFamilyDomain (n := n) f :=
    univ_Ico_subset_normalizedSquareFamily_smoothFamilyDomain F hM04 T τmax hτmax
      hwindow hcurvature p
  let U : Set (E × ℝ) := Set.univ ×ˢ Set.Ioo 0 τmax
  have hsqrt : ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ Real.sqrt z.2) U :=
    contDiff_snd.contDiffOn.sqrt (fun z hz ↦ hz.2.1.ne')
  have hmap : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓘(ℝ, E × ℝ)) ∞
      (fun z : E × ℝ ↦ (z.1, Real.sqrt z.2)) U :=
    (contDiff_fst.contDiffOn.prodMk hsqrt).contMDiffOn
  have hγ : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ normalizedBackwardFamily F T τmax p z.1 z.2) U := by
    apply (contMDiffOn_smoothFamilyDomain (n := n) f).comp hmap
    intro z hz
    exact hcontains ⟨Set.mem_univ _, Real.sqrt_nonneg z.2,
      Real.sqrt_lt_sqrt hz.2.1.le hz.2.2⟩
  refine ⟨{
    gamma := normalizedBackwardFamily F T τmax p
    gamma_at_zero := ?_
    path := paths
    path_eq := hpaths
    regularization := fun Z b hb hbmax ↦ Classical.choice (hregularizations Z b hb hbmax)
    squareFamily := normalizedSquareFamily F T τmax p
    squareDomain := smoothFamilyDomain (n := n) f
    square_open := isOpen_smoothFamilyDomain (n := n) f
    square_contains := hcontains
    square_smooth := ?_
    square_agrees := ?_
    square_at_zero := normalizedSquareFamily_zero F hM04 T τmax hτmax hwindow p
    initial_derivative := ?_
    gamma_smooth := ?_
  }⟩
  · intro Z
    simpa only [normalizedBackwardFamily, Real.sqrt_zero] using
      normalizedSquareFamily_zero F hM04 T τmax hτmax hwindow p Z
  · convert! (contMDiffOn_smoothFamilyDomain (n := n) f) using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  · intro Z s hs
    simp only [normalizedBackwardFamily, Real.sqrt_sq hs.1]
  · intro Z
    have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
        (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
      cases h
      rfl
    rw [hcast]
    exact congrArg (fun q : TangentBundle (𝓡 n) M ↦ (q.2 : V))
      (normalizedSquareFamily_initial_phase F hM04 T τmax hτmax hwindow p Z)
  · convert! hγ using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]

end PoincareConjecture.Proofs.M09
