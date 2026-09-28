import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPaths
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialPathFamily
import PoincareConjecture.Proofs.M76.Mathlib.PolygonProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition

set_option autoImplicit false

open Set Geometry

namespace Set

theorem IsCompact.exists_finitePL_disk_cut_of_proper_arc
    {C U V W : Set (ℝ × ℝ)} {a b : ℝ × ℝ}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hUV : U ∩ V ⊆ {a, b}) (hrim : U ∪ V = frontier C)
    (hproper : W \ {a, b} ⊆ interior C) :
    ∃ d₀ d₁ : Set (ℝ × ℝ),
      IsFinitePLBallPair (ℝ × ℝ) d₀ (U ∪ W) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (W ∪ V) ∧
      d₀ ∪ d₁ = C ∧ d₀ ∩ d₁ = W ∧
      d₀ ∩ frontier C = U ∧ d₁ ∩ frontier C = V := by
  classical
  let A : Fin 3 → Set (ℝ × ℝ) := ![U, V, W]
  have hA (i : Fin 3) : IsFinitePLBallPair ℝ (A i) {a, b} := by
    fin_cases i
    · exact hU
    · exact hV
    · exact hW
  choose n p hpi hp0 hp1 hcarrier hself hvertex using
    fun i => (hA i).exists_simplicial_path_with_endpoints hab
  have hWcontact : W ∩ (U ∪ V) ⊆ {a, b} := by
    intro x hx
    by_contra hnot
    have hfront : x ∈ frontier C := hrim ▸ hx.2
    exact hfront.2 (hproper ⟨hx.1, hnot⟩)
  have hcontact (i j : Fin 3) (hij : i ≠ j) : A i ∩ A j ⊆ {a, b} := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hUV
    · exact fun _ hx => hWcontact ⟨hx.2, Or.inl hx.1⟩
    · exact fun _ hx => hUV ⟨hx.2, hx.1⟩
    · exact (hij rfl).elim
    · exact fun _ hx => hWcontact ⟨hx.2, Or.inr hx.1⟩
    · exact fun _ hx => hWcontact ⟨hx.1, Or.inl hx.2⟩
    · exact fun _ hx => hWcontact ⟨hx.1, Or.inr hx.2⟩
    · exact (hij rfl).elim
  have hrange (i : Fin 3) : ({a, b} : Set (ℝ × ℝ)) ⊆ range (p i) := by
    intro x hx
    rcases hx with hx | hx
    · exact ⟨0, (hp0 i).trans hx.symm⟩
    · exact ⟨Fin.last (n i + 3), (hp1 i).trans hx.symm⟩
  have hcross (i j : Fin 3) (hij : i ≠ j) :
      Polygon.pathCarrier (p i) ∩ Polygon.pathCarrier (p j) ⊆ range (p i) ∩ range (p j) := by
    rw [hcarrier i, hcarrier j]
    exact (hcontact i j hij).trans (fun _ hx => ⟨hrange i hx, hrange j hx⟩)
  obtain ⟨K, _, hKedge, _⟩ := Polygon.exists_common_simplicial_path_complex
    (fun i => n i + 2) p hpi hself hvertex hcross
  let u := p 0
  let v : Fin (n 1 + 4) → ℝ × ℝ := fun i => p 1 i.rev
  let w := p 2
  have hu0 : u 0 = a := hp0 0
  have hu1 : u (Fin.last (n 0 + 3)) = b := hp1 0
  have hv0 : v 0 = b := by simpa only [v, Fin.rev_zero] using hp1 1
  have hv1 : v (Fin.last (n 1 + 3)) = a := by simpa only [v, Fin.rev_last] using hp0 1
  have hw0 : w 0 = a := hp0 2
  have hw1 : w (Fin.last (n 2 + 3)) = b := hp1 2
  have huv : u (Fin.last (n 0 + 3)) = v 0 := hu1.trans hv0.symm
  have hvu : v (Fin.last (n 1 + 3)) = u 0 := hv1.trans hu0.symm
  have huK : ∀ i : Fin (n 0 + 3),
      ({u i.castSucc, u i.succ} : Finset (ℝ × ℝ)) ∈ K.faces := hKedge 0
  have hvK : ∀ i : Fin (n 1 + 3),
      ({v i.castSucc, v i.succ} : Finset (ℝ × ℝ)) ∈ K.faces := by
    intro i
    simpa only [v, Fin.rev_castSucc, Fin.rev_succ, Finset.pair_comm] using hKedge 1 i.rev
  have hwK : ∀ i : Fin (n 2 + 3),
      ({w i.castSucc, w i.succ} : Finset (ℝ × ℝ)) ∈ K.faces := hKedge 2
  have huC : Polygon.pathCarrier u = U := hcarrier 0
  have hvC : Polygon.pathCarrier v = V := (Polygon.pathCarrier_reverse (p 1)).trans (hcarrier 1)
  have hwC : Polygon.pathCarrier w = W := hcarrier 2
  have hui : Function.Injective u := hpi 0
  have hvi : Function.Injective v := (hpi 1).comp Fin.rev_injective
  have hwi : Function.Injective w := hpi 2
  have hpaths : Polygon.pathCarrier u ∩ Polygon.pathCarrier v ⊆ {u 0, v 0} := by
    rw [huC, hvC, hu0, hv0]
    exact hUV
  let P := Polygon.ofPaths u v
  have hP : P.HasSimplicialEdges := Polygon.hasSimplicialEdges_ofPaths K u v huv hvu huK hvK
  have hiP : Function.Injective P := by
    apply Polygon.injective_ofPaths u v hui hvi huv hvu
    intro x hx
    obtain ⟨i, hi⟩ := hx.1
    obtain ⟨j, hj⟩ := hx.2
    exact hpaths ⟨hi ▸ Polygon.vertex_mem_pathCarrier u i,
      hj ▸ Polygon.vertex_mem_pathCarrier v j⟩
  have hfront : frontier C = P.boundary ℝ := by
    dsimp only [P]
    rw [Polygon.boundary_ofPaths u v huv hvu, huC, hvC]
    exact hrim.symm
  have hPC : closure P.inside = C :=
    P.closure_inside_eq_of_compact_convex hP hiP hC hcv hne hfront
  have hPi : interior C = P.inside := by
    rw [← hPC]
    exact P.interior_closure_inside hP hiP
  have hproper' : Polygon.pathCarrier w \ {u 0, v 0} ⊆ P.inside := by
    rw [hwC, hu0, hv0, ← hPi]
    exact hproper
  obtain ⟨d₀, d₁, hd₀, hd₁, hwhole, hcommon, houter₀, houter₁⟩ :=
    Polygon.exists_finitePL_disk_cut_of_paths K u v w hui hvi hwi huv hvu
      (hw0.trans hu0.symm) (hw1.trans hv0.symm) huK hvK hwK hpaths hproper'
  refine ⟨d₀, d₁, ?_, ?_, hwhole.trans hPC, hcommon.trans hwC, ?_, ?_⟩
  · simpa only [huC, hwC] using hd₀
  · simpa only [hwC, hvC] using hd₁
  · rw [hfront]
    exact houter₀.trans huC
  · rw [hfront]
    exact houter₁.trans hvC

end Set
