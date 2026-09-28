import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSpatialMap
import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

private theorem rebase_terminal_map
    {M : Type v} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (S : ℝ → GeneralizedSliceCarrier.{u}) {a b : ℝ} (hab : a = b)
    (e : OpenPartialHomeomorph M (S a).carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ∃ f : OpenPartialHomeomorph M (S b).carrier,
      f.source = e.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target ∧
      (⟨b, fun x => f x⟩ : (t : ℝ) × (M → (S t).carrier)) = ⟨a, fun x => e x⟩ ∧
      (⟨b, fun x => f.symm x⟩ : (t : ℝ) × ((S t).carrier → M)) =
        ⟨a, fun x => e.symm x⟩ := by
  cases hab
  exact ⟨e, rfl, he, hi, rfl, rfl⟩

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

private theorem exists_terminal_map (n : ℕ) :
    ∃ f : OpenPartialHomeomorph G.limit.sliceCarrier.carrier
        ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier,
      f.source = G.exhaustion.space n ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target ∧
      ∀ h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0,
        (⟨(V.base (G.subsequence n)).1, fun x => f x⟩ :
          (t : ℝ) × (G.limit.sliceCarrier.carrier →
            ((V.flow (G.subsequence n)).slice t).carrier)) =
          ⟨(V.base (G.subsequence n)).1 + 0 / V.scale (G.subsequence n),
            (G.embedding n).forward 0 h0⟩ ∧
        (⟨(V.base (G.subsequence n)).1, fun x => f.symm x⟩ :
          (t : ℝ) × (((V.flow (G.subsequence n)).slice t).carrier →
            G.limit.sliceCarrier.carrier)) =
          ⟨(V.base (G.subsequence n)).1 + 0 / V.scale (G.subsequence n),
            (G.embedding n).inverse 0 h0⟩ := by
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos n).le, le_rfl⟩
  let e := (G.embedding n).spatialOpenPartialHomeomorph (G.exhaustion.space_open n) 0 h0
  obtain ⟨f, hsource, hf, hi, hmap, hinv⟩ := rebase_terminal_map
    (V.flow (G.subsequence n)).slice
    (by simp : (V.base (G.subsequence n)).1 + 0 / V.scale (G.subsequence n) =
      (V.base (G.subsequence n)).1) e
    ((G.embedding n).spatialOpenPartialHomeomorph_contMDiffOn
      (G.exhaustion.space_open n) 0 h0)
    ((G.embedding n).spatialOpenPartialHomeomorph_symm_contMDiffOn
      (G.exhaustion.space_open n) 0 h0)
  exact ⟨f, hsource, hf, hi, fun _ => ⟨hmap, hinv⟩⟩

noncomputable def terminalCommonInterval_m30TerminalMap (n : ℕ) :
    OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
  (exists_terminal_map G n).choose

theorem terminalCommonInterval_m30_terminal_source (n : ℕ) :
    let f := terminalCommonInterval_m30TerminalMap G n
    f.source = G.exhaustion.space n ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target := by
  have h := (exists_terminal_map G n).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem terminalCommonInterval_m30_terminal_maps
    (n : ℕ) (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0) :
    let f := terminalCommonInterval_m30TerminalMap G n
    (⟨(V.base (G.subsequence n)).1, fun x => f x⟩ :
      (t : ℝ) × (G.limit.sliceCarrier.carrier →
        ((V.flow (G.subsequence n)).slice t).carrier)) =
      ⟨(V.base (G.subsequence n)).1 + 0 / V.scale (G.subsequence n),
        (G.embedding n).forward 0 h0⟩ ∧
    (⟨(V.base (G.subsequence n)).1, fun x => f.symm x⟩ :
      (t : ℝ) × (((V.flow (G.subsequence n)).slice t).carrier →
        G.limit.sliceCarrier.carrier)) =
      ⟨(V.base (G.subsequence n)).1 + 0 / V.scale (G.subsequence n),
        (G.embedding n).inverse 0 h0⟩ :=
  (exists_terminal_map G n).choose_spec.2.2.2 h0

theorem terminalCommonInterval_m30_terminal_base (n : ℕ) :
    terminalCommonInterval_m30TerminalMap G n G.limit.base = (V.base (G.subsequence n)).2 := by
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos n).le, le_rfl⟩
  have hmap := (terminalCommonInterval_m30_terminal_maps G n h0).1
  have hp := congrArg (fun z : (t : ℝ) × (G.limit.sliceCarrier.carrier →
      ((V.flow (G.subsequence n)).slice t).carrier) =>
      (⟨z.1, z.2 G.limit.base⟩ : (V.flow (G.subsequence n)).point)) hmap
  exact eq_of_heq (Sigma.mk.inj (hp.trans (G.base_preserving n h0))).2

theorem terminalCommonInterval_m30_terminal_inner
    (n : ℕ) (h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time n) 0)
    (x : G.limit.sliceCarrier.carrier) (v w : TangentSpace (𝓡 3) x) :
    let f := terminalCommonInterval_m30TerminalMap G n
    (M13.scaleSmoothMetric ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
      (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
      (G.embedding n).pullbackInner 0 h0 x v w := by
  have hmap := (terminalCommonInterval_m30_terminal_maps G n h0).1
  have hm := congrArg (fun z : (t : ℝ) × (G.limit.sliceCarrier.carrier →
      ((V.flow (G.subsequence n)).slice t).carrier) =>
      ((V.flow (G.subsequence n)).metric z.1).inner (z.2 x)
        (mfderiv (𝓡 3) (𝓡 3) z.2 x v) (mfderiv (𝓡 3) (𝓡 3) z.2 x w)) hmap
  exact congrArg (fun z : ℝ => V.scale (G.subsequence n) * z) hm

end PoincareConjecture.M47
