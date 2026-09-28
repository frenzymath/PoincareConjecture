import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Overlaps.Smooth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

theorem inverse_metric (e : OpenPartialHomeomorph X Y)
    (hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (hg : ∀ x ∈ e.source, ∀ a b : TangentSpace (𝓡 3) x,
      g.inner x a b = h.inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x a) (mfderiv (𝓡 3) (𝓡 3) e x b))
    (y : Y) (hy : y ∈ e.target) (a b : TangentSpace (𝓡 3) y) :
    h.inner y a b = g.inner (e.symm y)
      (mfderiv (𝓡 3) (𝓡 3) e.symm y a) (mfderiv (𝓡 3) (𝓡 3) e.symm y b) := by
  have hnear : (fun z => e (e.symm z)) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hf := ((hs _ (e.map_target hy)).contMDiffAt
    (e.open_source.mem_nhds (e.map_target hy))).mdifferentiableAt (by simp)
  have hinv := ((hi _ hy).contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp y hf hinv
  have hd (v : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) = v := by
    have he := hc.symm.trans (hnear.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3))
    calc
      _ = mfderiv (𝓡 3) (𝓡 3) id y v := congrArg (fun L => L v) he
      _ = v := by rw [mfderiv_id]; rfl
  have hm := hg _ (e.map_target hy)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y a) (mfderiv (𝓡 3) (𝓡 3) e.symm y b)
  have hm' : h.inner (e (e.symm y)) a b = g.inner (e.symm y)
      (mfderiv (𝓡 3) (𝓡 3) e.symm y a) (mfderiv (𝓡 3) (𝓡 3) e.symm y b) := by
    simpa only [hd a, hd b] using hm.symm
  exact (congrArg (fun z => h.inner z a b) (e.right_inv hy)).symm.trans hm'

variable {ι : Type u} {Z : ι → Type v}
  [∀ i, TopologicalSpace (Z i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Z i)]
  [∀ i, IsManifold (𝓡 3) ∞ (Z i)]
  (e : ∀ i, OpenPartialHomeomorph X (Z i))
  (hd : Pairwise (fun i j => Disjoint (e i).source (e j).source))
  (hs : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i) (e i).source)
  (hi : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i).symm (e i).target)
  (g : RiemannianMetric 3 X) (h : ∀ i, RiemannianMetric 3 (Z i))
  (hg : ∀ i x, x ∈ (e i).source → ∀ a b : TangentSpace (𝓡 3) x,
    g.inner x a b = (h i).inner (e i x)
      (mfderiv (𝓡 3) (𝓡 3) (e i) x a) (mfderiv (𝓡 3) (𝓡 3) (e i) x b))

def pieceMetric : ∀ i : Option ι, RiemannianMetric 3 (Piece X Z i)
  | none => g
  | some i => h i

include hs hi hg in
theorem overlaps_metric (i j : Option ι) (x : Piece X Z i)
    (hx : x ∈ ((overlaps e hd).transition i j).source)
    (a b : TangentSpace (𝓡 3) x) :
    (pieceMetric g h i).inner x a b =
      (pieceMetric g h j).inner ((overlaps e hd).transition i j x)
        (mfderiv (𝓡 3) (𝓡 3) ((overlaps e hd).transition i j) x a)
        (mfderiv (𝓡 3) (𝓡 3) ((overlaps e hd).transition i j) x b) := by
  cases i with
  | none =>
    cases j with
    | none =>
      change g.inner x a b = g.inner x
        (mfderiv (𝓡 3) (𝓡 3) id x a) (mfderiv (𝓡 3) (𝓡 3) id x b)
      rw [mfderiv_id]
      rfl
    | some j => exact hg j x hx a b
  | some i =>
    cases j with
    | none => exact inverse_metric (e i) (hs i) (hi i) g (h i) (hg i) x hx a b
    | some j =>
      by_cases hij : i = j
      · subst j
        rw [(overlaps e hd).self (some i)]
        change (h i).inner x a b = (h i).inner x
          (mfderiv (𝓡 3) (𝓡 3) id x a) (mfderiv (𝓡 3) (𝓡 3) id x b)
        rw [mfderiv_id]
        rfl
      · change x ∈ (capTransition e i j).source at hx
        rw [capTransition_source_empty e hd hij] at hx
        exact hx.elim

end PoincareConjecture.Surgery.Terminal.Gluing
