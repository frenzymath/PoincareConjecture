import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.OpenPartialHomeomorph.Composition










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u v w u' v' w'

namespace OpenPartialHomeomorph

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {H : Type v} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {K : Type w} [TopologicalSpace K] [ChartedSpace H K]
  [IsManifold I ∞ K] [CompactSpace K]
  {E' : Type u'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type v'} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type w'} [TopologicalSpace M] [ChartedSpace H' M]
  [IsManifold J ∞ M]


set_option linter.unusedSectionVars false in



theorem exists_normalized_graph_strip_chart
    (e : OpenPartialHomeomorph (K × ℝ) M) (f g : K → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g)
    (hlt : ∀ q : K, f q < g q)
    (hstrip : {z : K × ℝ | f z.1 ≤ z.2 ∧ z.2 ≤ g z.1} ⊆ e.source)
    (he : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ e e.source)
    (hei : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target) :
    ∃ delta : ℝ, 0 < delta ∧ delta < 1 / 8 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ delta →
        ∃ c : OpenPartialHomeomorph (K × ℝ) M,
          c.source = univ ×ˢ Ioo (-eta) (1 + eta) ∧
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ c c.source ∧
          ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ c.symm c.target ∧
          (∀ z : K × ℝ,
            c z = e (z.1, f z.1 + z.2 * (g z.1 - f z.1))) ∧
          c '' (univ ×ˢ Icc (0 : ℝ) 1) =
            e '' {z : K × ℝ | f z.1 ≤ z.2 ∧ z.2 ≤ g z.1} ∧
          range (fun q : K => c (q, 0)) = range (fun q : K => e (q, f q)) ∧
          range (fun q : K => c (q, 1)) = range (fun q : K => e (q, g q)) := by
  have hwidth (q : K) : 0 < g q - f q := sub_pos.mpr (hlt q)
  let F : K × ℝ → ℝ := fun z => f z.1 + z.2 * (g z.1 - f z.1)
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F :=
    (hf.comp contMDiff_fst).add
      (contMDiff_snd.mul ((hg.comp contMDiff_fst).sub (hf.comp contMDiff_fst)))
  have hpos (q : K) (s : ℝ) : 0 < deriv (fun t : ℝ => F (q, t)) s := by
    have hd : HasDerivAt (fun t : ℝ => F (q, t)) (g q - f q) s := by
      simpa only [F, one_mul, id_eq] using
        (((hasDerivAt_id s).mul_const (g q - f q)).const_add (f q))
    rw [hd.deriv]
    exact hwidth q
  have hsurj (q : K) : Function.Surjective (fun t : ℝ => F (q, t)) := by
    intro s
    refine ⟨(s - f q) / (g q - f q), ?_⟩
    dsimp only [F]
    rw [div_mul_cancel₀ _ (ne_of_gt (hwidth q))]
    ring
  obtain ⟨D, hD, _⟩ :=
    Diffeomorph.exists_fiberwise_of_deriv_pos (Diffeomorph.refl I K ∞) F hF hpos hsurj
  have hDforward (z : K × ℝ) : D z = (z.1, F z) := hD z
  let b := D.toHomeomorph.toOpenPartialHomeomorph.trans e
  have hb : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) J ∞ b b.source :=
    he.comp D.contMDiff.contMDiffOn (fun _ hz => hz.2)
  have hbi : ContMDiffOn J (I.prod 𝓘(ℝ, ℝ)) ∞ b.symm b.target :=
    D.symm.contMDiff.comp_contMDiffOn (hei.mono (fun _ hz => hz.1))
  have hFclosed {z : K × ℝ} (hz : z ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      f z.1 ≤ F z ∧ F z ≤ g z.1 := by
    have hlo := mul_nonneg hz.2.1 (hwidth z.1).le
    have hhi := mul_nonneg (sub_nonneg.mpr hz.2.2) (hwidth z.1).le
    dsimp only [F]
    constructor <;> nlinarith
  have hclosed : univ ×ˢ Icc (0 : ℝ) 1 ⊆ b.source := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change D z ∈ e.source
    rw [hDforward]
    exact hstrip (hFclosed hz)
  obtain ⟨U, V, _, hV, hU, hI, hUV⟩ :=
    generalized_tube_lemma (isCompact_univ : IsCompact (univ : Set K))
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)) b.open_source hclosed
  obtain ⟨r0, hr0, hball0⟩ :=
    Metric.mem_nhds_iff.mp (hV.mem_nhds (hI (show (0 : ℝ) ∈ Icc 0 1 by norm_num)))
  obtain ⟨r1, hr1, hball1⟩ :=
    Metric.mem_nhds_iff.mp (hV.mem_nhds (hI (show (1 : ℝ) ∈ Icc 0 1 by norm_num)))
  let m : ℝ := min r0 (min r1 (1 / 8))
  have hm : 0 < m := by dsimp only [m]; positivity
  have hm0 : m ≤ r0 := min_le_left _ _
  have hm1 : m ≤ r1 := (min_le_right _ _).trans (min_le_left _ _)
  have hm8 : m ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let delta : ℝ := m / 2
  have hdpos : 0 < delta := by dsimp only [delta]; positivity
  have hd0 : delta < r0 := by dsimp only [delta]; linarith
  have hd1 : delta < r1 := by dsimp only [delta]; linarith
  have hd8 : delta < 1 / 8 := by dsimp only [delta]; linarith
  have hwide : univ ×ˢ Ioo (-delta) (1 + delta) ⊆ b.source := by
    intro z hz
    apply hUV
    refine ⟨hU (mem_univ _), ?_⟩
    by_cases hlo : z.2 < 0
    · apply hball0
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith [hz.2.1], by linarith⟩
    by_cases hhi : 1 < z.2
    · apply hball1
      rw [Metric.mem_ball, Real.dist_eq]
      exact abs_lt.mpr ⟨by linarith, by linarith [hz.2.2]⟩
    exact hI ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩
  refine ⟨delta, hdpos, hd8, ?_⟩
  intro eta _heta heta
  let S : Set (K × ℝ) := univ ×ˢ Ioo (-eta) (1 + eta)
  have hS : S ⊆ b.source := by
    intro z hz
    exact hwide ⟨mem_univ _, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  let c := b.restrOpen S hSopen
  have hcforward (z : K × ℝ) :
      c z = e (z.1, f z.1 + z.2 * (g z.1 - f z.1)) := by
    change e (D z) = _
    rw [hDforward]
  refine ⟨c, inter_eq_right.mpr hS, hb.mono inter_subset_left,
    hbi.mono inter_subset_left, hcforward, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact ⟨(z.1, F z), hFclosed hz, (hcforward z).symm⟩
    · rintro x ⟨z, hz, rfl⟩
      let t : ℝ := (z.2 - f z.1) / (g z.1 - f z.1)
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz.1) (hwidth z.1).le
      have ht1 : t ≤ 1 := (div_le_one (hwidth z.1)).mpr (by linarith [hz.2])
      refine ⟨(z.1, t), ⟨mem_univ _, ht0, ht1⟩, ?_⟩
      rw [hcforward]
      congr 1
      apply Prod.ext
      · rfl
      dsimp only [t]
      rw [div_mul_cancel₀ _ (ne_of_gt (hwidth z.1))]
      ring
  · congr 1
    funext q
    rw [hcforward]
    simp
  · congr 1
    funext q
    rw [hcforward]
    simp

end OpenPartialHomeomorph
