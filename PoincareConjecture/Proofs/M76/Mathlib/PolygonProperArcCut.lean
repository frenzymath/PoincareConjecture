import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathRegionPartition

set_option autoImplicit false

open Set Geometry

namespace Polygon

theorem exists_finitePL_disk_cut_of_paths {m n k : ℕ}
    (K : SimplicialComplex ℝ (ℝ × ℝ))
    (u : Fin (m + 4) → ℝ × ℝ) (v : Fin (n + 4) → ℝ × ℝ)
    (w : Fin (k + 4) → ℝ × ℝ)
    (hu : Function.Injective u) (hv : Function.Injective v) (hw : Function.Injective w)
    (huv : u (Fin.last (m + 3)) = v 0)
    (hvu : v (Fin.last (n + 3)) = u 0)
    (hwu : w 0 = u 0) (hwv : w (Fin.last (k + 3)) = v 0)
    (huK : ∀ i : Fin (m + 3), ({u i.castSucc, u i.succ} : Finset (ℝ × ℝ)) ∈ K.faces)
    (hvK : ∀ i : Fin (n + 3), ({v i.castSucc, v i.succ} : Finset (ℝ × ℝ)) ∈ K.faces)
    (hwK : ∀ i : Fin (k + 3), ({w i.castSucc, w i.succ} : Finset (ℝ × ℝ)) ∈ K.faces)
    (hinter : pathCarrier u ∩ pathCarrier v ⊆ {u 0, v 0})
    (hproper : pathCarrier w \ {u 0, v 0} ⊆ (ofPaths u v).inside) :
    ∃ d₀ d₁ : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) d₀ (pathCarrier u ∪ pathCarrier w) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (pathCarrier w ∪ pathCarrier v) ∧
      d₀ ∪ d₁ = closure (ofPaths u v).inside ∧
      d₀ ∩ d₁ = pathCarrier w ∧
      d₀ ∩ (ofPaths u v).boundary ℝ = pathCarrier u ∧
      d₁ ∩ (ofPaths u v).boundary ℝ = pathCarrier v := by
  classical
  let P := ofPaths u v
  let Q := ofPaths u (fun i => w i.rev)
  let R := ofPaths w v
  have hrange {j : ℕ} (a : Fin (j + 2) → ℝ × ℝ) : range a ⊆ pathCarrier a := by
    rintro _ ⟨i, rfl⟩
    exact vertex_mem_pathCarrier a i
  have hP : P.HasSimplicialEdges := hasSimplicialEdges_ofPaths K u v huv hvu huK hvK
  have hiP : Function.Injective P := injective_ofPaths u v hu hv huv hvu
    ((inter_subset_inter (hrange u) (hrange v)).trans hinter)
  have hPb : P.boundary ℝ = pathCarrier u ∪ pathCarrier v := boundary_ofPaths u v huv hvu
  have hwend : {u 0, v 0} ⊆ pathCarrier w := by
    rintro x (rfl | hx)
    · rw [← hwu]
      exact vertex_mem_pathCarrier w 0
    · have hx' : x = v 0 := hx
      rw [hx', ← hwv]
      exact vertex_mem_pathCarrier w (Fin.last (k + 3))
  have hendsu : {u 0, v 0} ⊆ pathCarrier u := by
    rintro x (rfl | hx)
    · exact vertex_mem_pathCarrier u 0
    · have hx' : x = v 0 := hx
      rw [hx', ← huv]
      exact vertex_mem_pathCarrier u (Fin.last (m + 3))
  have hendsv : {u 0, v 0} ⊆ pathCarrier v := by
    rintro x (rfl | hx)
    · rw [← hvu]
      exact vertex_mem_pathCarrier v (Fin.last (n + 3))
    · have hx' : x = v 0 := hx
      rw [hx']
      exact vertex_mem_pathCarrier v 0
  have hwcontact : pathCarrier w ∩ (pathCarrier u ∪ pathCarrier v) ⊆ {u 0, v 0} := by
    intro x hx
    by_contra hn
    exact (hproper ⟨hx.1, hn⟩).1 (hPb.symm ▸ hx.2)
  have hwP : pathCarrier w ⊆ closure P.inside := by
    intro x hx
    by_cases he : x ∈ ({u 0, v 0} : Set (ℝ × ℝ))
    · apply frontier_subset_closure
      rw [P.frontier_inside hP hiP, hPb]
      exact Or.inl (hendsu he)
    · exact subset_closure (hproper ⟨hx, he⟩)
  have huv' : u (Fin.last (m + 3)) = (fun i : Fin (k + 4) => w i.rev) 0 := by
    simpa only [Fin.rev_zero] using huv.trans hwv.symm
  have hvu' : (fun i => w i.rev) (Fin.last (k + 3)) = u 0 := by
    simpa only [Fin.rev_last] using hwu
  have hwK' : ∀ i : Fin (k + 3),
      ({w i.castSucc.rev, w i.succ.rev} : Finset (ℝ × ℝ)) ∈ K.faces := by
    intro i
    simpa only [Fin.rev_castSucc, Fin.rev_succ, Finset.pair_comm] using hwK i.rev
  have hQ : Q.HasSimplicialEdges :=
    hasSimplicialEdges_ofPaths K u (fun i => w i.rev) huv' hvu' huK hwK'
  have hR : R.HasSimplicialEdges :=
    hasSimplicialEdges_ofPaths K w v hwv (hvu.trans hwu.symm) hwK hvK
  have hiQ : Function.Injective Q := by
    apply injective_ofPaths u (fun i => w i.rev) hu (hw.comp Fin.rev_injective) huv' hvu'
    intro x hx
    have hxw : x ∈ pathCarrier w := by
      rw [← pathCarrier_reverse w]
      exact hrange (fun i => w i.rev) hx.2
    simpa only [Fin.rev_zero, hwv] using hwcontact ⟨hxw, Or.inl (hrange u hx.1)⟩
  have hiR : Function.Injective R := by
    apply injective_ofPaths w v hw hv hwv (hvu.trans hwu.symm)
    intro x hx
    simpa only [hwu] using hwcontact ⟨hrange w hx.1, Or.inr (hrange v hx.2)⟩
  obtain ⟨_, hwhole, hcommon⟩ := region_partition_three_paths u v w huv hvu hwu hwv
    hP hiP hQ hiQ hR hiR hwP (hinter.trans hwend)
  have hQb : Q.boundary ℝ = pathCarrier u ∪ pathCarrier w := by
    dsimp only [Q]
    rw [boundary_ofPaths u (fun i => w i.rev) huv' hvu', pathCarrier_reverse]
  have hRb : R.boundary ℝ = pathCarrier w ∪ pathCarrier v :=
    boundary_ofPaths w v hwv (hvu.trans hwu.symm)
  have hd₀ : IsFinitePLBallPair (ℝ × ℝ) (closure Q.inside) (pathCarrier u ∪ pathCarrier w) := by
    rw [← hQb]
    exact Q.isFinitePLBallPair_closed_inside hQ hiQ
  have hd₁ : IsFinitePLBallPair (ℝ × ℝ) (closure R.inside) (pathCarrier w ∪ pathCarrier v) := by
    rw [← hRb]
    exact R.isFinitePLBallPair_closed_inside hR hiR
  refine ⟨closure Q.inside, closure R.inside, hd₀, hd₁, hwhole.symm, hcommon, ?_, ?_⟩
  · rw [hPb]
    ext x
    constructor
    · rintro ⟨hx, hu' | hv'⟩
      · exact hu'
      · have hxw : x ∈ pathCarrier w := hcommon ▸ And.intro hx (hd₁.1 (Or.inr hv'))
        exact hendsu (hwcontact ⟨hxw, Or.inr hv'⟩)
    · exact fun hx => ⟨hd₀.1 (Or.inl hx), Or.inl hx⟩
  · rw [hPb]
    ext x
    constructor
    · rintro ⟨hx, hu' | hv'⟩
      · have hxw : x ∈ pathCarrier w := hcommon ▸ And.intro (hd₀.1 (Or.inl hu')) hx
        exact hendsv (hwcontact ⟨hxw, Or.inl hu'⟩)
      · exact hv'
    · exact fun hx => ⟨hd₁.1 (Or.inr hx), Or.inr hx⟩

end Polygon
