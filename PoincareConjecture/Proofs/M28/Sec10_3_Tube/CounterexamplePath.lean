import PoincareConjecture.Proofs.M28.Thm10_2_Counterexamples
import PoincareConjecture.Proofs.M28.Generalized.ShortPaths
import PoincareConjecture.Proofs.M28.Generalized.CanonicalAdapters
import PoincareConjecture.Proofs.M28.Generalized.Rescaling

set_option autoImplicit false
set_option linter.style.haveILetI false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M28

structure CounterexamplePathSegment
    {epsilon C A D₀ D : ℝ}
    (E : SameTimeCounterexample.{u} epsilon C A D₀ D) where
  path : ℝ → (E.flow.slice E.time).carrier
  path_zero : path 0 = E.basepoint
  path_one : path 1 = E.endpoint
  path_smooth : ContMDiff 𝓘(ℝ) (𝓡 3) 1 path
  path_length :
    (E.flow.metric E.time).pathELength path 0 1 <
      ENNReal.ofReal (A * E.flow.scalar ⟨E.time, E.basepoint⟩ ^ (-1 / 2 : ℝ))
  level_parameter : ℝ
  level_mem : level_parameter ∈ Icc (0 : ℝ) 1
  level_eq :
    E.flow.scalar ⟨E.time, path level_parameter⟩ =
      4 * E.flow.scalar ⟨E.time, E.basepoint⟩
  canonical_after : ∀ v ∈ Icc level_parameter 1,
    Nonempty (GeneralizedCanonicalControl (F := E.flow) E.time
      (path v) epsilon C)
  suffix_length :
    (E.flow.metric E.time).pathELength path level_parameter 1 <
      ENNReal.ofReal (A * E.flow.scalar ⟨E.time, E.basepoint⟩ ^ (-1 / 2 : ℝ))

theorem exists_counterexample_path_segment
    (P : RicciFlowCurvatureTheory.{u})
    {epsilon C A D₀ D : ℝ}
    (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
    (hD₀ : 0 < D₀) (hD : 4 ≤ D) :
    Nonempty (CounterexamplePathSegment E) := by
  let Q : ℝ := E.flow.scalar ⟨E.time, E.basepoint⟩
  have hQ : 0 < Q := lt_of_lt_of_le hD₀ E.base_lower
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength, _, _⟩ :=
    (E.flow.metric E.time).exists_short_path_of_mem_ball E.endpoint_mem
  have hstart : E.flow.scalar ⟨E.time, γ 0⟩ ≤ 4 * Q := by
    rw [hγ0]
    dsimp [Q]
    nlinarith
  have hend : 4 * Q < E.flow.scalar ⟨E.time, γ 1⟩ := by
    rw [hγ1]
    dsimp [Q]
    have hprod : 4 * Q ≤ D * Q := mul_le_mul_of_nonneg_right hD hQ.le
    nlinarith [E.scalar_large, hprod]
  obtain ⟨s, hs, hlevel, hcanonical⟩ :=
    generalizedSliceStrongCanonicalNeighborhoods.path_last_level
      P E.canonical γ hγsmooth.continuous.continuousOn hstart hend
  have hsuffix :
      (E.flow.metric E.time).pathELength γ s 1 <
        ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) := by
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
      ⟨(E.flow.metric E.time).toRiemannianMetric⟩
    exact (Manifold.pathELength_mono hs.1 le_rfl).trans_lt hγlength
  refine ⟨{
    path := γ
    path_zero := hγ0
    path_one := hγ1
    path_smooth := hγsmooth
    path_length := by simpa [Q] using hγlength
    level_parameter := s
    level_mem := hs
    level_eq := by simpa [Q] using hlevel
    canonical_after := hcanonical
    suffix_length := by simpa [Q] using hsuffix }⟩

theorem rescale_scalar_at_zero
    (F : GeneralizedRicciFlowData.{u}) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (z : (rescale F Q hQ a).slice 0 |>.carrier) :
    (rescale F Q hQ a).scalar ⟨0, z⟩ =
      F.scalar ⟨parabolicTimeInv Q a 0, z⟩ / Q := by
  exact rescale_scalar F Q hQ a 0 z

theorem rescale_edist_at_zero
    (F : GeneralizedRicciFlowData.{u}) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x y : (rescale F Q hQ a).slice 0 |>.carrier) :
    ((rescale F Q hQ a).metric 0).edist x y =
      ENNReal.ofReal (Real.sqrt Q) *
        (F.metric (parabolicTimeInv Q a 0)).edist x y := by
  exact rescale_edist F Q hQ a 0 x y

end PoincareConjecture.M28
