import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompactSegment
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicLocalPaths
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicSplicing
import Mathlib.Topology.UnitInterval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle unitInterval

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_intrinsic_minimizer_of_metric_segment (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {p q : M} {η : ℝ → M}
    (hη0 : η 0 = p) (hη1 : η 1 = q)
    (hη : ContinuousOn η (Icc (0 : ℝ) 1))
    (hηU : MapsTo η (Icc (0 : ℝ) 1) (U : Set M))
    (hsegment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      intrinsicEDist g (U : Set M) (η s) (η t) =
        ENNReal.ofReal |s - t| * intrinsicEDist g (U : Set M) p q) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) ∧
      g.pathELength γ 0 1 = intrinsicEDist g (U : Set M) p q := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  choose W hWopen hxW hWU hpaths using fun x : U =>
    exists_open_intrinsic_minimizing_paths g U.isOpen x.property
  let c (x : U) : Set unitInterval := (fun t : unitInterval => η t) ⁻¹' W x
  have hcopen (x : U) : IsOpen (c x) := (hWopen x).preimage hη.domRestrict
  have hcover : (univ : Set unitInterval) ⊆ ⋃ x : U, c x := by
    intro t _
    exact mem_iUnion.mpr ⟨⟨η t, hηU t.property⟩, hxW _⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hcover
  let D := intrinsicEDist g (U : Set M) p q
  have hpaths' (k : ℕ) : ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = η (t k) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) ∧
      g.pathELength γ 0 1 = ENNReal.ofReal (t k : ℝ) * D := by
    induction k with
    | zero =>
        refine ⟨fun _ => p, rfl, ?_, contMDiff_const.contMDiffOn, ?_, ?_⟩
        · simpa only [ht0, Set.Icc.coe_zero] using hη0.symm
        · intro s _
          exact hη0 ▸ hηU (by norm_num)
        · simp [ht0, RiemannianMetric.pathELength, Manifold.pathELength]
    | succ k ih =>
        obtain ⟨α, hα0, hα1, hα, hαU, hαlength⟩ := ih
        obtain ⟨x, hx⟩ := hsub k
        have hleft : η (t k) ∈ W x := hx ⟨le_rfl, hmono (Nat.le_succ k)⟩
        have hright : η (t (k + 1)) ∈ W x := hx ⟨hmono (Nat.le_succ k), le_rfl⟩
        obtain ⟨β, hβ0, hβ1, hβ, hβU, hβlength⟩ := hpaths x _ hleft _ hright
        obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlength⟩ :=
          exists_intrinsic_splice g hα hβ hαU hβU (hα1.trans hβ0.symm)
        refine ⟨γ, hγ0.trans hα0, hγ1.trans hβ1, hγ, hγU, ?_⟩
        have hstep : (t k : ℝ) ≤ (t (k + 1) : ℝ) := hmono (Nat.le_succ k)
        have hdiff : 0 ≤ (t (k + 1) : ℝ) - (t k : ℝ) := sub_nonneg.mpr hstep
        rw [hsegment (t k) (t k).property (t (k + 1)) (t (k + 1)).property,
          abs_sub_comm, abs_of_nonneg hdiff] at hβlength
        rw [hγlength, hαlength, hβlength, ← add_mul,
          ← ENNReal.ofReal_add (t k).property.1 hdiff]
        have hsum : (t k : ℝ) + ((t (k + 1) : ℝ) - (t k : ℝ)) =
            (t (k + 1) : ℝ) := by ring
        rw [hsum]
  obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlength⟩ := hpaths' n
  have htn : t n = 1 := hn n le_rfl
  refine ⟨γ, hγ0, ?_, hγ, hγU, ?_⟩
  · exact hγ1.trans (by simpa only [htn, Set.Icc.coe_one] using hη1)
  · simpa only [htn, Set.Icc.coe_one, ENNReal.ofReal_one, one_mul] using hγlength

theorem exists_intrinsic_minimizer_of_compact_sequence
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    {p q : M} {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    {L : ℝ} {paths : ℕ → ℝ → M}
    (hpaths : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1))
    (h0 : ∀ k, paths k 0 = p) (h1 : ∀ k, paths k 1 = q)
    (hconf : ∀ k, MapsTo (paths k) (Icc (0 : ℝ) 1) K)
    (hbound : ∀ k, g.pathELength (paths k) 0 1 < ENNReal.ofReal L)
    (hlength : Tendsto (fun k => g.pathELength (paths k) 0 1) atTop
      (𝓝 (intrinsicEDist g (U : Set M) p q))) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) ∧
      g.pathELength γ 0 1 = intrinsicEDist g (U : Set M) p q ∧
      g.pathELength γ 0 1 ≠ ⊤ := by
  obtain ⟨η, hη0, hη1, hη, hηK, hsegment⟩ :=
    exists_intrinsic_metric_segment_of_compact_sequence g U hK hKU hpaths h0 h1
      hconf hbound hlength
  obtain ⟨γ, hγ0, hγ1, hγ, hγU, hγlength⟩ :=
    exists_intrinsic_minimizer_of_metric_segment g U hη0 hη1 hη
      (fun t ht => hKU (hηK ht)) hsegment
  refine ⟨γ, hγ0, hγ1, hγ, hγU, hγlength, ?_⟩
  rw [hγlength]
  have hle := intrinsicEDist_le_pathELength g zero_le_one (hpaths 0)
    (fun t ht => hKU (hconf 0 ht))
  rw [h0 0, h1 0] at hle
  exact ne_top_of_lt ((hle.trans_lt (hbound 0)).trans_le le_top)

end PoincareConjecture.M28
