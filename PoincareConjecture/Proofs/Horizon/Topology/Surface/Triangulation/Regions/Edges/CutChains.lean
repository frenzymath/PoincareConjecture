


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.OrientedSubdivision
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Transversals








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

omit [T2Space M] in



theorem exists_oriented_graph_cut_chain (e : D.EdgeIndex) (R : D.regions)
    (C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target)
    {m : ℕ} (c : Fin (m + 2) → ℝ) (hc : StrictMono c)
    (A : Fin (m + 1) → EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ))
    (G : Fin (m + 1) → OpenPartialHomeomorph ℝ ℝ)
    (f : Fin (m + 1) → ℝ → ℝ)
    (hG : ∀ i, ContDiffOn ℝ ∞ (G i) (G i).source)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (G i).target)
    (hsource : ∀ i, Icc (c i.castSucc) (c i.succ) ⊆ (G i).source)
    (hgraph_source : ∀ i x, x ∈ (G i).target → (A i).symm (x, f i x) ∈ C.source)
    (hgraph : ∀ i t, t ∈ (G i).source →
      (D.edge e.1 e.2).map t = C ((A i).symm (G i t, f i (G i t))))
    (hprojection : ∀ i t, t ∈ Icc (c i.castSucc) (c i.succ) →
      0 < (A i (deriv (C.symm ∘ (D.edge e.1 e.2).map) t)).1)
    (α β δ : Fin (m + 1) → ℝ) (hδ : ∀ i, 0 < δ i)
    (hendtube : ∀ i, G i (c i.castSucc) ∈ Ioo (α i) (β i) ∧
      G i (c i.succ) ∈ Ioo (α i) (β i))
    (htube : ∀ i x, x ∈ Ioo (α i) (β i) → ∀ z : ℝ, |z| < δ i →
      (A i).symm (x, f i x + z) ∈ C.source ∧
      (C ((A i).symm (x, f i x + z)) ∈ connectedComponentIn
        (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z))
    (dLeft dRight : EuclideanSpace ℝ (Fin 2))
    (hLeft : 0 < (A 0 dLeft).2 - deriv (f 0) (G 0 (c 0)) * (A 0 dLeft).1)
    (hRight : 0 < (A (Fin.last m) dRight).2 -
      deriv (f (Fin.last m)) (G (Fin.last m) (c (Fin.last (m + 1)))) *
        (A (Fin.last m) dRight).1) :
    ∃ (d : Fin (m + 2) → EuclideanSpace ℝ (Fin 2))
      (ℓ : Fin m → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ),
      d 0 = dLeft ∧ d (Fin.last (m + 1)) = dRight ∧
      (∀ j, d j ≠ 0) ∧
      (∀ i, 0 < (A i (d i.castSucc)).2 -
          deriv (f i) (G i (c i.castSucc)) * (A i (d i.castSucc)).1 ∧
        0 < (A i (d i.succ)).2 -
          deriv (f i) (G i (c i.succ)) * (A i (d i.succ)).1) ∧
      ∀ i : Fin m,
        d i.castSucc.succ = (A i.castSucc).symm (0, 1) ∧
        ℓ i (d i.castSucc.succ) = 0 ∧
        0 < ℓ i ((A i.castSucc).symm
          (1, deriv (f i.castSucc) (G i.castSucc (c i.castSucc.succ)))) ∧
        0 < ℓ i ((A i.succ).symm
          (1, deriv (f i.succ) (G i.succ (c i.castSucc.succ)))) ∧
        ∀ᶠ r in 𝓝[>] (0 : ℝ),
          C.symm ((D.edge e.1 e.2).map (c i.castSucc.succ)) + r • d i.castSucc.succ ∈ C.source ∧
          C (C.symm ((D.edge e.1 e.2).map (c i.castSucc.succ)) + r • d i.castSucc.succ) ∈
            connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
  have hstep (i : Fin (m + 1)) : c i.castSucc ≤ c i.succ :=
    (hc Fin.castSucc_lt_succ).le
  have hinternal : ∀ i : Fin m,
      ∃ (d : EuclideanSpace ℝ (Fin 2)) (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ),
        d = (A i.castSucc).symm (0, 1) ∧ d ≠ 0 ∧
        0 < (A i.castSucc d).2 -
          deriv (f i.castSucc) (G i.castSucc (c i.castSucc.succ)) * (A i.castSucc d).1 ∧
        0 < (A i.succ d).2 -
          deriv (f i.succ) (G i.succ (c i.castSucc.succ)) * (A i.succ d).1 ∧
        ℓ d = 0 ∧
        0 < ℓ ((A i.castSucc).symm
          (1, deriv (f i.castSucc) (G i.castSucc (c i.castSucc.succ)))) ∧
        0 < ℓ ((A i.succ).symm
          (1, deriv (f i.succ) (G i.succ (c i.castSucc.succ)))) ∧
        ∀ᶠ r in 𝓝[>] (0 : ℝ),
          C.symm ((D.edge e.1 e.2).map (c i.castSucc.succ)) + r • d ∈ C.source ∧
          C (C.symm ((D.edge e.1 e.2).map (c i.castSucc.succ)) + r • d) ∈
            connectedComponentIn (chartDiskBoundaryUnion D.centers D.radius)ᶜ R := by
    intro i
    have htleft : c i.castSucc.succ ∈ Icc (c i.castSucc.castSucc) (c i.castSucc.succ) :=
      right_mem_Icc.mpr (hstep i.castSucc)
    have htright : c i.castSucc.succ ∈ Icc (c i.succ.castSucc) (c i.succ.succ) :=
      left_mem_Icc.mpr (hstep i.succ)
    obtain ⟨d, ℓ, hd, hne, _, htransA, htransB, hzero, hposA, hposB, hray⟩ :=
      D.exists_common_graph_transversal e R C hCinv (A i.castSucc) (A i.succ)
        (G i.castSucc) (G i.succ) (f i.castSucc) (f i.succ)
        (hG i.castSucc) (hG i.succ) (hf i.castSucc) (hf i.succ)
        (hgraph_source i.castSucc) (hgraph_source i.succ)
        (hgraph i.castSucc) (hgraph i.succ)
        (hsource i.castSucc htleft) (hsource i.succ htright)
        (hprojection i.castSucc _ htleft) (hprojection i.succ _ htright)
        (hendtube i.castSucc).2 (hendtube i.succ).1 (hδ i.castSucc) (hδ i.succ)
        (htube i.castSucc) (htube i.succ)
    exact ⟨d, ℓ, hd, hne, by rw [htransA]; exact zero_lt_one,
      htransB, hzero, hposA, hposB, hray⟩
  choose innerDirection ℓ hinner using hinternal
  let d : Fin (m + 2) → EuclideanSpace ℝ (Fin 2) :=
    Fin.cases dLeft (Fin.lastCases dRight innerDirection)
  have hfirst : d 0 = dLeft := rfl
  have hlast : d (Fin.last (m + 1)) = dRight := by
    change Fin.cases dLeft (Fin.lastCases dRight innerDirection) (Fin.last m).succ = dRight
    rw [Fin.cases_succ, Fin.lastCases_last]
  have hmiddle (i : Fin m) : d i.castSucc.succ = innerDirection i := by simp [d]
  have hleft_ne : dLeft ≠ 0 := by intro he; simp [he] at hLeft
  have hright_ne : dRight ≠ 0 := by intro he; simp [he] at hRight
  have hnonzero : ∀ j, d j ≠ 0 := by
    intro j
    refine Fin.cases hleft_ne (fun k => ?_) j
    change (Fin.lastCases dRight innerDirection k : EuclideanSpace ℝ (Fin 2)) ≠ 0
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simpa only [Fin.lastCases_last] using hright_ne
    · simpa only [Fin.lastCases_castSucc] using (hinner i).2.1
  have hpositive_left : ∀ i : Fin (m + 1),
      0 < (A i (d i.castSucc)).2 -
        deriv (f i) (G i (c i.castSucc)) * (A i (d i.castSucc)).1 := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa only [Fin.castSucc_zero, hfirst] using hLeft
    · rw [Fin.castSucc_succ, hmiddle]
      exact (hinner i).2.2.2.1
  have hpositive_right : ∀ i : Fin (m + 1),
      0 < (A i (d i.succ)).2 -
        deriv (f i) (G i (c i.succ)) * (A i (d i.succ)).1 := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [Fin.succ_last, hlast] using hRight
    · rw [hmiddle]
      exact (hinner i).2.2.1
  refine ⟨d, ℓ, hfirst, hlast, hnonzero, fun i => ⟨hpositive_left i, hpositive_right i⟩, ?_⟩
  intro i
  rw [hmiddle]
  exact ⟨(hinner i).1, (hinner i).2.2.2.2⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
