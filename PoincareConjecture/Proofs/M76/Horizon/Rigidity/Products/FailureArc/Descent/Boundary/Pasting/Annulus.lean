import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting









set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem NestedShellSquareCharts.exists_target_map_union
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {S T : Set P2} {D : NestedShellDissection S T} (C : NestedShellSquareCharts D)
    (f : Fin 2 → P2 → X) (hf : ∀ j, PolyhedralPLInCharts e (f j) Sq)
    (hleft : ∀ t : I, f 0 (0, t) = f 1 (0, t))
    (hright : ∀ t : I, f 0 (1, t) = f 1 (1, t)) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g (T \ interior S) ∧
      (∀ j (z : Sq), g (C.chart j z) = f j z) ∧
      g '' (T \ interior S) = f 0 '' Sq ∪ f 1 '' Sq := by
  classical
  have hinverse (j : Fin 2) : ∃ q : P2 → P2,
      FinitePiecewiseAffineOn q (D.disk j) ∧
      ∀ z : D.disk j, ((C.chart j).symm z : P2) = q z := (C.finitePL j).symm
  choose q hq hqval using hinverse
  have hpieces (j : Fin 2) : ∃ K : SimplicialComplex ℝ P2,
      K.faces.Finite ∧ K.space = D.disk j ∧
      PolyhedralPLInCharts e (f j ∘ q j) K.space := by
    obtain ⟨K, hK, hKs, hAff⟩ := hq j
    refine ⟨K, hK, hKs, (hf j).comp_finitePiecewiseAffineOn K hK
      ⟨K, hK, rfl, hAff⟩ ?_⟩
    intro x hx
    rw [← hqval j ⟨x, hKs.subset hx⟩]
    exact ((C.chart j).symm ⟨x, hKs.subset hx⟩).property
  choose K hK hKs hPL using hpieces
  have hagree : ∀ x ∈ (K 0).space, x ∈ (K 1).space →
      (f 0 ∘ q 0) x = (f 1 ∘ q 1) x := by
    intro x hx₀ hx₁
    let z := (C.chart 0).symm ⟨x, (hKs 0).subset hx₀⟩
    have hsame : q 1 x = z := (hqval 1 ⟨x, (hKs 1).subset hx₁⟩).symm.trans
      (congrArg Subtype.val (C.inverse_agree ((hKs 0).subset hx₀)
        ((hKs 1).subset hx₁))).symm
    have hzside : (z : P2).1 = 0 ∨ (z : P2).1 = 1 := by
      apply (C.mem_other_disk_iff z).mp
      simpa only [z, Homeomorph.apply_symm_apply] using (hKs 1).subset hx₁
    change f 0 (q 0 x) = f 1 (q 1 x)
    rw [← hqval 0 ⟨x, (hKs 0).subset hx₀⟩, hsame]
    change f 0 z = f 1 z
    rcases hzside with hz | hz
    · rw [show (z : P2) = (0, z.val.2) from Prod.ext hz rfl]
      exact hleft ⟨z.val.2, z.property.2⟩
    · rw [show (z : P2) = (1, z.val.2) from Prod.ext hz rfl]
      exact hright ⟨z.val.2, z.property.2⟩
  obtain ⟨g, hg, hg₀, hg₁⟩ := Dehn.exists_circle_attachment_map_union
    hcompat (K 0) (K 1) (hK 0) (hK 1) (hPL 0) (hPL 1) hagree
  have hwhole : (K 0).space ∪ (K 1).space = T \ interior S := by
    rw [hKs 0, hKs 1, D.disk_cover]
  have hval (j : Fin 2) (z : Sq) : g (C.chart j z) = f j z := by
    have hj : EqOn g (f j ∘ q j) (K j).space := by fin_cases j <;> assumption
    rw [hj ((hKs j).symm.subset (C.chart j z).property)]
    change f j (q j (C.chart j z)) = f j z
    rw [← hqval j (C.chart j z), Homeomorph.symm_apply_apply]
  refine ⟨g, hwhole ▸ hg, hval, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases D.disk_cover.symm.subset hx with hx | hx
    · let z := (C.chart 0).symm ⟨x, hx⟩
      exact Or.inl ⟨z, z.property, (hval 0 z).symm.trans
        (congrArg g (congrArg Subtype.val ((C.chart 0).apply_symm_apply ⟨x, hx⟩)))⟩
    · let z := (C.chart 1).symm ⟨x, hx⟩
      exact Or.inr ⟨z, z.property, (hval 1 z).symm.trans
        (congrArg g (congrArg Subtype.val ((C.chart 1).apply_symm_apply ⟨x, hx⟩)))⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨C.chart 0 ⟨z, hz⟩,
        D.disk_cover.subset (Or.inl (C.chart 0 ⟨z, hz⟩).property), hval 0 ⟨z, hz⟩⟩
    · exact ⟨C.chart 1 ⟨z, hz⟩,
        D.disk_cover.subset (Or.inr (C.chart 1 ⟨z, hz⟩).property), hval 1 ⟨z, hz⟩⟩



theorem exists_standard_annulus_map_of_square_pair
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X F}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (f : Fin 2 → P2 → X) (hf : ∀ j, PolyhedralPLInCharts e (f j) Sq)
    (hleft : ∀ t : I, f 0 (0, t) = f 1 (0, t))
    (hright : ∀ t : I, f 0 (1, t) = f 1 (1, t)) :
    ∃ (P : Fin 2 → Set P2) (c : ∀ j, Sq ≃ₜ P j) (g : P2 → X),
      PolyhedralPLInCharts e g (squareAnnulus 8 1) ∧
      (∀ j, (c j).IsFinitePL) ∧ P 0 ∪ P 1 = squareAnnulus 8 1 ∧
      (∀ j (z : Sq), g (c j z) = f j z) ∧
      (∀ j (z : Sq), depth 8 (c j z : P2) = -1 ↔ (z : P2).2 = 0) ∧
      (∀ j (z : Sq), depth 8 (c j z : P2) = 1 ↔ (z : P2).2 = 1) ∧
      g '' squareAnnulus 8 1 = f 0 '' Sq ∪ f 1 '' Sq := by
  let S : Set P2 := Dehn.annulusSquare 8 1
  let T : Set P2 := Dehn.annulusSquare 8 (-1)
  have hS : IsFinitePLBallPair P2 S (frontier S) :=
    Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hT : IsFinitePLBallPair P2 T (frontier T) :=
    Dehn.isFinitePLBallPair_annulusSquare (by norm_num)
  have hST : S ⊆ interior T := by
    intro z hz
    have hh := (Dehn.mem_annulusSquare_iff 8 1 z).mp hz
    apply (Dehn.mem_interior_annulusSquare_iff 8 (-1) z).mpr
    linarith
  have hAnn : T \ interior S = squareAnnulus 8 1 := by
    ext z
    rw [mem_sdiff, Dehn.mem_annulusSquare_iff, Dehn.mem_interior_annulusSquare_iff,
      mem_squareAnnulus_iff_depth, mem_Icc]
    exact and_congr_right (fun _ ↦ not_lt)
  obtain ⟨D⟩ := exists_nested_shell_dissection hS hT hST
  obtain ⟨C⟩ := D.nonempty_square_charts
  obtain ⟨g, hg, hval, him⟩ := C.exists_target_map_union hcompat f hf hleft hright
  refine ⟨D.disk, C.chart, g, hAnn ▸ hg, C.finitePL,
    D.disk_cover.trans hAnn, hval, ?_, ?_, hAnn ▸ him⟩
  · intro j z
    exact (Dehn.mem_frontier_annulusSquare_iff 8 (-1) (C.chart j z)).symm.trans
      ((D.outer_in_disk_iff j (C.chart j z)).trans (C.outer_iff j z))
  · intro j z
    exact (Dehn.mem_frontier_annulusSquare_iff 8 1 (C.chart j z)).symm.trans
      ((D.inner_in_disk_iff j (C.chart j z)).trans (C.inner_iff j z))

end PoincareConjecture.M76.Dehn
