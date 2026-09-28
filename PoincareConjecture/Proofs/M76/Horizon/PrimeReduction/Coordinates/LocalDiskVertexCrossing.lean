import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.LocalDiskSignedLink
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcCrossedStar
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInteriorChart
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBirthStar










set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem exists_vertex_crossing_chart_of_local_disk
    (K L : SimplicialComplex ℝ C3) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hbound : ∀ a ∈ L.faces, a.card ≤ 3)
    (hp : (0 : C3) ∈ L.vertices) (hint : (0 : C3) ∈ interior K.space)
    {d rim : Set C3} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdL : d ⊆ L.space) (hpd : (0 : C3) ∈ d \ rim)
    (hopen : IsOpen ((Subtype.val : L.space → C3) ⁻¹' (d \ rim)))
    {u v : C3} (hu : u ≠ 0) (hv : v ≠ 0)
    (hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0})
    (hlocal : ∀ᶠ x in 𝓝 (0 : C3),
      x ∈ L.space ∩ {x | x.2 = 0} ↔ x ∈ segment ℝ 0 u ∪ segment ℝ 0 v)
    (hneg : (0 : C3) ∈ closure (L.space ∩ {x | x.2 < 0}))
    (hpos : (0 : C3) ∈ closure (L.space ∩ {x | 0 < x.2}))
    {O : Set C3} (hO : IsOpen O) (hpO : (0 : C3) ∈ O) :
    ∃ H : OpenPartialHomeomorph C3 C3,
      (0 : C3) ∈ H.source ∧ H.source ⊆ O ∧ H 0 = 0 ∧
      H ∈ piecewiseAffineGroupoid C3 ∧
      (∀ x ∈ H.source, x ∈ L.space ↔ (H x).2 = 0) ∧
      (∀ x ∈ H.source, x.2 = 0 ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, 0 ≤ x.2 ↔ 0 ≤ (H x).1.1 := by
  classical
  have hL : L.faces.Finite := hK.subset hLK
  have hpK : (0 : C3) ∈ K.vertices := hLK hp
  let A : C3 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
  obtain ⟨n, P, hPi, hP, hPs, hcount, _, _, _, _, hn, hpositive⟩ :=
    L.exists_signed_link_polygon_of_local_disk_and_section hL hbound hp hd hdL hpd hopen
      A hu hv hinter hlocal hneg hpos
  have hlink : (L.link 0) ≤ K.link 0 :=
    fun a ha => ⟨hLK ha.1, ha.2.1, hLK ha.2.2⟩
  obtain ⟨a, b, hab, hzero⟩ := Set.ncard_eq_two.mp hcount
  have hPK : P.boundary ℝ ⊆ (K.link 0).space :=
    hPs.subset.trans (space_subset_of_le hlink)
  have hPn : ∃ x ∈ P.boundary ℝ, x.2 < 0 := by
    obtain ⟨x, hx, hn⟩ := hn
    exact ⟨x, hPs.symm.subset ((L.link 0).vertices_subset_space hx), hn⟩
  have hPp : ∃ x ∈ P.boundary ℝ, 0 < x.2 := by
    obtain ⟨x, hx, hn⟩ := hpositive
    exact ⟨x, hPs.symm.subset ((L.link 0).vertices_subset_space hx), hn⟩
  have haP : a ∈ P.boundary ℝ := hPs.symm.subset (hzero.symm.subset (by simp)).1
  obtain ⟨C, g, F, _, _, _, _, hF, _, hFg, hg0, _, _, _, hFzero, hFpos, hFsheet⟩ :=
    PoincareConjecture.M76.Dehn.exists_original_crossed_star K hK hpK hint P hP hPi hPK hab
      (by simpa [hPs, A] using hzero) hPn hPp
  have hcone : (L.closedStar 0).space = convexJoin ℝ {0} (P.boundary ℝ) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hx0 : x = 0
      · exact (mem_convexJoin_zero_iff _ _).mpr
          ⟨a, haP, 0, by simp, by simpa only [zero_smul] using hx0⟩
      · obtain ⟨z, hz, r, hr, hxr⟩ := exists_linkPoint_smul hx hx0
        exact (mem_convexJoin_zero_iff _ _).mpr
          ⟨z, hPs.symm.subset hz, r, ⟨hr.1.le, hr.2⟩, hxr⟩
    · intro x hx
      obtain ⟨z, hz, r, hr, rfl⟩ := (mem_convexJoin_zero_iff _ _).mp hx
      exact L.smul_mem_closedStar_zero
        (space_subset_of_le (L.link_le_closedStar 0) (hPs.subset hz)) hr
  obtain ⟨δ, hδ, hLstar⟩ := L.exists_ball_inter_space_subset_closedStar hL hp
  obtain ⟨η, hη, hKstar⟩ := K.exists_ball_inter_space_subset_closedStar hK hpK
  have hstarint : (0 : C3) ∈ interior (K.closedStar 0).space := by
    apply interior_maximal
      (show interior K.space ∩ Metric.ball 0 η ⊆ (K.closedStar 0).space from
        fun _ hx => hKstar ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.inter Metric.isOpen_ball)
    exact ⟨hint, Metric.mem_ball_self hη⟩
  obtain ⟨B, hBs, _, hB, hBinv, _, _, hBF, _⟩ := hF.exists_interior_chart rfl
  let U := O ∩ Metric.ball (0 : C3) δ
  have hU : IsOpen U := hO.inter Metric.isOpen_ball
  let H := B.restrOpen U hU
  have hHsource : H.source = B.source ∩ U := rfl
  have hHforward (x : C3) : H x = B x := rfl
  have hwhole (x : C3) (hx : x ∈ H.source) : x ∈ L.space ↔
      x ∈ convexJoin ℝ {0} (P.boundary ℝ) := by
    rw [← hcone]
    exact ⟨fun h => hLstar ⟨h, hx.2.2⟩,
      fun h => space_subset_of_le (show L.closedStar 0 ≤ L from fun _ hs => hs.1) h⟩
  have hval (x : C3) (hx : x ∈ H.source) :
      H x = (F ⟨x, interior_subset (hBs.subset hx.1)⟩ : C3) :=
    hBF ⟨x, interior_subset (hBs.subset hx.1)⟩
  refine ⟨H, ⟨hBs.symm.subset hstarint, hpO, Metric.mem_ball_self hδ⟩,
    fun _ hx => hx.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · change B 0 = 0
    rw [hBF ⟨0, interior_subset hstarint⟩, hFg, hg0]
  · exact ⟨hB.mono H.open_source inter_subset_left,
      hBinv.mono H.open_target inter_subset_left⟩
  · intro x hx
    rw [hval x hx]
    exact (hwhole x hx).trans (hFsheet ⟨x, interior_subset (hBs.subset hx.1)⟩)
  · intro x hx
    rw [hval x hx]
    exact hFzero ⟨x, interior_subset (hBs.subset hx.1)⟩
  · intro x hx
    rw [hval x hx]
    exact hFpos ⟨x, interior_subset (hBs.subset hx.1)⟩

end Geometry.SimplicialComplex
