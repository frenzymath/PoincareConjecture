import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.CutBandIncidence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.OneBoundaryDisk
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.CountZeroAnnulus
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.Counts.ComponentEulerSum



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open scoped BigOperators

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1
local notation "Band" => squareAnnulus 1 (1 / 8)
local notation "Ann" => squareAnnulus 8 1

open Classical in
set_option maxHeartbeats 800000 in



theorem exists_selected_cut_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (N : Bool → Set E) (hN : ∀ b, IsClosed (N b))
    (hdisN : Disjoint (N false) (N true))
    (hconn : IsPreconnected (K.space ∪ ⋃ b, N b))
    (c : ∀ b, Band ≃ₜ N b)
    (hcut : ∀ b x, (c b x : E) ∈ K.space ↔
      depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8)
    (B : Bool × Bool → SimplicialComplex ℝ E) (hBK : ∀ i, B i ≤ K)
    (gamma : ∀ i, Q2 ≃ₜ (B i).space) (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hdis : Pairwise (fun i j ↦ Disjoint (B i).space (B j).space))
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (B i).faces then 1 else 2)
    (hlevel : ∀ i x, (c i.1 x : E) ∈ (B i).space ↔
      depth 1 x = if i.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    (htotal : 0 ≤ K.surfaceEulerCount)
    (hnoDisk : ∀ i (T : Set E), T ⊆ K.space →
      ¬ IsFinitePLBallPair (ℝ × ℝ) T (B i).space) :
    ∃ (r : Bool → Bool → K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) (s t : Bool)
      (H : Ann ≃ₜ (K.edgeComponentComplex D).space),
      (∀ b u, B (b, u) ≤ K.edgeComponentComplex (r b u)) ∧
      componentRims r D = {(false, s), (true, t)} ∧
      H.IsFinitePL ∧
      (∀ x, (H x : E) ∈ (B (false, s)).space ↔ depth 8 x = -1) ∧
      ∀ x, (H x : E) ∈ (B (true, t)).space ↔ depth 8 x = 1 := by
  classical
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let : Fintype K.vertexAbstractComplex.edgeGraph.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨r₀, hr₀, hbound₀⟩ := exists_component_boundary_euler_bounds K hK hpure hlinks
    B hBK hdis gamma hgamma (by
      intro a ha hac
      convert hcofaces a ha hac using 1
      split_ifs <;> rfl)
  obtain ⟨r₁, hr₁, hgraph₁, hhit₁⟩ := exists_connected_cut_band_assignment K hK
    N hN hdisN hconn c hcut B hBK gamma hgamma hlevel
  let r := fun b u ↦ r₀ (b, u)
  have hre : r = r₁ := by
    funext b u
    obtain ⟨x, hx⟩ := (circle_incidence (B (b, u)) (hK.subset (hBK (b, u)))
      (gamma (b, u)) (hgamma (b, u))).2.2.1.nonempty
    exact (mem_component_of_assigned_rim_iff K (B (b, u)) (r b u) (r₁ b u)
      (hr₀ (b, u)) hx).mp (SimplicialComplex.space_subset_of_le (hr₁ b u) hx)
  have hcard (D) : Nat.card {i // r₀ i = D} = (componentRims r D).card :=
    Nat.subtype_card _ (by intro i; simp only [componentRims, Finset.mem_filter,
      Finset.mem_univ, true_and]; rfl)
  have hbound (D) : (K.edgeComponentComplex D).surfaceEulerCount ≤
      2 - ((componentRims r D).card : ℤ) := by
    simpa only [hcard D] using hbound₀ D
  have hface (D) (a) (ha : a ∈ (K.edgeComponentComplex D).faces)
      (i) (hi : a ∈ (B i).faces) : r₀ i = D := by
    obtain ⟨v, hv⟩ := (B i).nonempty_of_mem_faces hi
    exact (mem_component_of_assigned_rim_iff K (B i) (r₀ i) D (hr₀ i)
      ((B i).subset_space hi hv)).mp ((K.edgeComponentComplex D).subset_space ha hv)
  have hpureD (D) : ∀ a ∈ (K.edgeComponentComplex D).faces,
      ∃ t ∈ (K.edgeComponentComplex D).faces, t.card = 3 ∧ a ⊆ t := by
    intro a ha
    obtain ⟨t, ht, htc, hat⟩ := hpure a ha.1
    exact ⟨t, K.edgeComponentComplex_coface D ha ht hat, htc, hat⟩
  have hlinksD (D) : ∀ v ∈ (K.edgeComponentComplex D).vertices,
      IsConnected ((K.edgeComponentComplex D).link v).space := by
    intro v hv
    rw [← SimplicialComplex.faceLink_singleton_eq_link,
      K.edgeComponentComplex_vertex_link D hv, SimplicialComplex.faceLink_singleton_eq_link]
    exact hlinks v hv.1
  have hnodisk (D) (hd : (componentRims r D).card = 1) :
      (K.edgeComponentComplex D).surfaceEulerCount ≠ 1 := by
    intro hcount
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hd
    have hir : r₀ i = D := by
      have hmem : i ∈ componentRims r D := hi.symm ▸ Finset.mem_singleton_self i
      simpa only [componentRims, Finset.mem_filter, Finset.mem_univ, true_and, r] using hmem
    have hBi : B i ≤ K.edgeComponentComplex D := by simpa only [hir] using hr₀ i
    have hb : ∀ a ∈ (K.edgeComponentComplex D).faces, a.card = 2 →
        {t | t ∈ (K.edgeComponentComplex D).faces ∧ t.card = 3 ∧ a ⊆ t}.ncard =
          if a ∈ (B i).faces then 1 else 2 := by
      intro a ha hac
      have hm : (∃ j, a ∈ (B j).faces) ↔ a ∈ (B i).faces := by
        constructor
        · rintro ⟨j, hj⟩
          have hjr : j ∈ componentRims r D := by
            simpa only [componentRims, Finset.mem_filter, Finset.mem_univ, true_and, r] using
              hface D a ha j hj
          rw [hi, Finset.mem_singleton] at hjr
          exact hjr ▸ hj
        · exact fun h ↦ ⟨i, h⟩
      rw [K.edgeComponentComplex_cofaces D ha 3, hcofaces a ha.1 hac]
      simp only [hm]
    exact hnoDisk i _ (SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D))
      (isFinitePLBallPair_of_one_boundary_count_one (K.edgeComponentComplex D) (B i)
        (hK.subset (K.edgeComponentComplex_le D)) (hpureD D) (hlinksD D)
        (K.edgeComponentComplex_isPathConnected D).isConnected hcount hBi
        (gamma i) (hgamma i) hb)
  have hsum : 0 ≤ ∑ D, (K.edgeComponentComplex D).surfaceEulerCount := by
    rwa [← K.surfaceEulerCount_eq_sum_edgeComponents hK]
  obtain ⟨_, D, s, t, hzero, hrs, hrt, hselected⟩ := exists_two_rim_count_zero_component r
    (hre.symm ▸ hgraph₁) (hre.symm ▸ hhit₁)
    (fun D ↦ (K.edgeComponentComplex D).surfaceEulerCount) hbound hnodisk hsum
  let pick : Bool → Bool × Bool := fun b ↦ if b then (true, t) else (false, s)
  have hpick (b) : r₀ (pick b) = D := by cases b <;> assumption
  have hBD (b) : B (pick b) ≤ K.edgeComponentComplex D := by
    simpa only [hpick b] using hr₀ (pick b)
  have hbD : ∀ a ∈ (K.edgeComponentComplex D).faces, a.card = 2 →
      {v | v ∈ (K.edgeComponentComplex D).faces ∧ v.card = 3 ∧ a ⊆ v}.ncard =
        if ∃ b, a ∈ (B (pick b)).faces then 1 else 2 := by
    intro a ha hac
    have hm : (∃ i, a ∈ (B i).faces) ↔ ∃ b, a ∈ (B (pick b)).faces := by
      constructor
      · rintro ⟨i, hi⟩
        have hir : i ∈ componentRims r D := by
          simpa only [componentRims, Finset.mem_filter, Finset.mem_univ, true_and, r] using
            hface D a ha i hi
        rw [hselected, Finset.mem_insert, Finset.mem_singleton] at hir
        rcases hir with rfl | rfl
        · exact ⟨false, hi⟩
        · exact ⟨true, hi⟩
      · rintro ⟨b, hb⟩
        exact ⟨pick b, hb⟩
    rw [K.edgeComponentComplex_cofaces D ha 3, hcofaces a ha.1 hac]
    simp only [hm]
  obtain ⟨H, hH, hH0, hH1⟩ := exists_annulus_of_count_zero (K.edgeComponentComplex D)
    (hK.subset (K.edgeComponentComplex_le D)) (hpureD D) (hlinksD D)
    (K.edgeComponentComplex_isPathConnected D).isConnected hzero (fun b ↦ B (pick b)) hBD
    (fun b ↦ gamma (pick b)) (fun b ↦ hgamma (pick b))
    (hdis (by simp [pick])) hbD
  exact ⟨r, D, s, t, H, fun b u ↦ hr₀ (b, u), hselected, hH,
    fun x ↦ (hH0 x).symm, fun x ↦ (hH1 x).symm⟩

end PoincareConjecture.M76.Dehn.Annuli
