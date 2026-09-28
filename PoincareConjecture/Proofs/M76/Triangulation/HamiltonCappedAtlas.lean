import PoincareConjecture.Proofs.M76.Triangulation.HamiltonOpenInclusionSphere
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapOriginalAtlasCompatibility
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedCapInteriorCompatibility
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonCapRetainedCompatibility
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonBrownInteriorChart

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "M" => (ℝ × (Fin 2 → ℝ))

variable {X : Type*} [TopologicalSpace X]

private theorem cap_restrict_compatible
    (c d : OpenPartialHomeomorph X V3)
    (h : c.symm.trans d ∈ piecewiseAffineGroupoid V3)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) :
    (c.restrOpen U hU).symm.trans (d.restrOpen V hV) ∈ piecewiseAffineGroupoid V3 := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp h).mono
    ((c.restrOpen U hU).symm.trans (d.restrOpen V hV)).open_source
    (fun _ hx => ⟨hx.1.1, hx.2.1⟩)

private theorem cap_restrict_left_compatible
    (c d : OpenPartialHomeomorph X V3)
    (h : c.symm.trans d ∈ piecewiseAffineGroupoid V3)
    {U : Set X} (hU : IsOpen U) :
    (c.restrOpen U hU).symm.trans d ∈ piecewiseAffineGroupoid V3 := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp h).mono
    ((c.restrOpen U hU).symm.trans d).open_source (fun _ hx => ⟨hx.1.1, hx.2⟩)

private theorem cap_compatible_symm
    {c d : OpenPartialHomeomorph X V3}
    (h : c.symm.trans d ∈ piecewiseAffineGroupoid V3) :
    d.symm.trans c ∈ piecewiseAffineGroupoid V3 := by
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm h

private theorem cap_disjoint_compatible
    (c d : OpenPartialHomeomorph X V3) (h : Disjoint c.source d.source) :
    c.symm.trans d ∈ piecewiseAffineGroupoid V3 := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply LocallyPiecewiseAffineOn.locality
  intro p hp
  exact False.elim (Set.disjoint_left.mp h (c.map_target hp.1) hp.2)

theorem exists_marked_brown_cap_PL_domain
    {Y : Set X} [Nonempty Y] (hY : IsOpen Y)
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph Y V3) {K S : Set Y}
    (hKD : PLDomain e K) (s : ChartwisePLSphere e S)
    {H D : Set X} (d : κ → OpenPartialHomeomorph X V3) (hd : PLDomain d H)
    (hD : IsClosed D) (hfront : frontier D = (Subtype.val : Y → X) '' S)
    (hSK : S ⊆ frontier K) {N : Set Y} (hN : IsOpen N) (hSN : S ⊆ N)
    (hlocal : ∀ y ∈ N, (y : X) ∈ D ↔ y ∉ interior K)
    (hball : IsUnitBallPair V3 D ((Subtype.val : Y → X) '' S))
    {V O : Set X} (hV : IsOpen V) (hO : IsOpen O) (hDV : D ⊆ V)
    (hVO : Disjoint V O) (hboundary : frontier H ⊆ O)
    (holdCover : H \ D ⊆ Y) (houter : Hᶜ ⊆ O) :
    let j : OpenPartialHomeomorph Y X :=
      hY.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : Y → X)
    (∀ i l, (j.symm.trans (e i)).symm.trans ((d l).restrOpen O hO) ∈
      piecewiseAffineGroupoid V3) →
    ∃ charts : Set (OpenPartialHomeomorph X V3),
      PLDomain (fun c : charts => (c : OpenPartialHomeomorph X V3)) H ∧
      (∀ i, (j.symm.trans (e i)).restrOpen Dᶜ hD.isOpen_compl ∈ charts) ∧
      ∀ l, (d l).restrOpen O hO ∈ charts := by
  classical
  dsimp only
  let j : OpenPartialHomeomorph Y X :=
    hY.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : Y → X)
  have hjs : j.source = univ := rfl
  have hj (y : Y) : y ∈ j.source := by rw [hjs]; exact mem_univ y
  let ew : ι → OpenPartialHomeomorph X V3 := fun i => j.symm.trans (e i)
  let outer : κ → OpenPartialHomeomorph X V3 := fun l => (d l).restrOpen O hO
  intro hcollar
  have hews (i : ι) : (ew i).source = (Subtype.val : Y → X) '' (e i).source := by
    ext x
    constructor
    · intro hx
      exact ⟨j.symm x, hx.2, j.right_inv hx.1⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨j.map_source (hj y), ?_⟩
      change j.symm (j y) ∈ (e i).source
      rw [j.left_inv (hj y)]
      exact hy
  have hewval (i : ι) (y : Y) : ew i y = e i y := by
    change e i (j.symm (j y)) = e i y
    rw [j.left_inv (hj y)]
  have hew (i l : ι) : (ew i).symm.trans (ew l) ∈ piecewiseAffineGroupoid V3 := by
    apply OpenPartialHomeomorph.affine_inclusion_transition_mem_piecewiseAffineGroupoid
      (Subtype.val : Y → X) Subtype.val_injective (e i) (e l) (hKD.compatible i l)
      (ContinuousAffineEquiv.refl ℝ V3) (ContinuousAffineEquiv.refl ℝ V3) (ew i) (ew l)
    · intro p hp
      exact ⟨hp.1, rfl⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (hews l).subset hx
      exact ⟨y, hy, rfl, hewval l y⟩
  obtain ⟨sw, _, _⟩ := s.exists_open_inclusion hY
  let sD : ChartwisePLSphere ew (frontier D) := {
    parametrization := sw.parametrization.trans (Homeomorph.setCongr hfront.symm)
    map := sw.map
    map_eq := sw.map_eq
    piecewiseAffine := sw.piecewiseAffine }
  have hballD : IsUnitBallPair V3 D (frontier D) := by rw [hfront]; exact hball
  obtain ⟨phi, U, g, _, hphiboundary, _, hU, hgval, _, hgzero, hgS⟩ :=
    exists_marked_brown_inward_collar hballD sD.parametrization
  obtain ⟨C, hCs, _, hCval, _⟩ :=
    exists_marked_brown_interior_chart phi rfl hphiboundary
  have hg (p : frontier D × Ico (0 : ℝ) (1 / 8)) : ((g p : D) : X) ∈ D :=
    (g p : D).property
  have hCg (p : frontier D × Ico (0 : ℝ) (1 / 8)) : C ((g p : D) : X) =
      unitCubeInwardCollarMap ((sD.parametrization.symm p.1 : V3), (p.2 : ℝ)) := by
    rw [hCval]
    exact hgval p
  choose B a c hB hcsource hcval hcinv hcpoint using
    fun y : S => hKD.exists_marked_cap_coordinates_in_open_ambient hY hD y
      (hSK y.property) N hN (hSN y.property) hlocal (by norm_num : (0 : ℝ) < 1 / 8)
      hU g hgzero hgS
  let q : M ≃ᴬ[ℝ] V3 := (Fin.consEquivL ℝ (fun _ : Fin 3 => ℝ)).toContinuousAffineEquiv
  let cap0 : S → OpenPartialHomeomorph X V3 :=
    fun y => (c y).chart.transHomeomorph q.toHomeomorph
  let cap : S → OpenPartialHomeomorph X V3 := fun y => (cap0 y).restrOpen V hV
  let old : ι → OpenPartialHomeomorph X V3 :=
    fun i => (ew i).restrOpen Dᶜ hD.isOpen_compl
  have hnormalized (y : S) (i : ι) : (ew i).symm.trans
      ((c y).original.transHomeomorph (a y).symm.toHomeomorph) ∈
        piecewiseAffineGroupoid V3 := by
    apply OpenPartialHomeomorph.affine_inclusion_transition_mem_piecewiseAffineGroupoid
      (Subtype.val : Y → X) Subtype.val_injective (e i) (B y) (hB y i)
      (ContinuousAffineEquiv.refl ℝ V3) (ContinuousAffineEquiv.refl ℝ V3) (ew i)
      ((c y).original.transHomeomorph (a y).symm.toHomeomorph)
    · intro p hp
      exact ⟨hp.1, rfl⟩
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := (hcsource y).subset hx
      refine ⟨z, hz.1, rfl, ?_⟩
      change (a y).symm ((c y).original z) = B y z
      rw [hcval y z hz, (a y).symm_apply_apply]
  have hcapold (y : S) (i : ι) : (cap y).symm.trans (old i) ∈
      piecewiseAffineGroupoid V3 :=
    cap_restrict_left_compatible (cap0 y) (old i)
      ((c y).retained_compatible (a y).symm q (ew i)
        (cap_compatible_symm (hnormalized y i)) hD hg) hV
  have hcapC (y : S) : (cap y).symm.trans C ∈ piecewiseAffineGroupoid V3 :=
    cap_restrict_left_compatible (cap0 y) C
      ((c y).interior_compatible sD (a y).symm q C (hnormalized y) hg hCs hCg) hV
  have hcapcap (y z : S) : (cap y).symm.trans (cap z) ∈ piecewiseAffineGroupoid V3 :=
    cap_restrict_compatible (cap0 y) (cap0 z)
      (hKD.marked_cap_charts_compatible g (c y) (c z) (B y) (B z)
        (hB y) (hB z) (a y) (a z) (hcinv y) (hcsource z) (hcval z) q) hV hV
  have holdold (i l : ι) : (old i).symm.trans (old l) ∈ piecewiseAffineGroupoid V3 :=
    cap_restrict_compatible (ew i) (ew l) (hew i l) hD.isOpen_compl hD.isOpen_compl
  have holdouter (i : ι) (l : κ) : (old i).symm.trans (outer l) ∈
      piecewiseAffineGroupoid V3 :=
    cap_restrict_left_compatible (ew i) (outer l) (hcollar i l) hD.isOpen_compl
  have houterouter (i l : κ) : (outer i).symm.trans (outer l) ∈
      piecewiseAffineGroupoid V3 :=
    cap_restrict_compatible (d i) (d l) (hd.compatible i l) hO hO
  have holdC (i : ι) : (old i).symm.trans C ∈ piecewiseAffineGroupoid V3 := by
    apply cap_disjoint_compatible
    apply Set.disjoint_left.mpr
    intro x hx hxC
    exact hx.2 (interior_subset (hCs.subset hxC))
  have hcapouter (y : S) (l : κ) : (cap y).symm.trans (outer l) ∈
      piecewiseAffineGroupoid V3 := by
    apply cap_disjoint_compatible
    exact Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp hVO hx.2 hy.2)
  have hCouter (l : κ) : C.symm.trans (outer l) ∈ piecewiseAffineGroupoid V3 := by
    apply cap_disjoint_compatible
    exact Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp hVO (hDV (interior_subset (hCs.subset hx))) hy.2)
  let f : (ι ⊕ S ⊕ Unit ⊕ κ) → OpenPartialHomeomorph X V3 :=
    Sum.elim old (Sum.elim cap (Sum.elim (fun _ => C) outer))
  have hf (i l : ι ⊕ S ⊕ Unit ⊕ κ) : (f i).symm.trans (f l) ∈
      piecewiseAffineGroupoid V3 := by
    rcases i with i | i | i | i <;> rcases l with l | l | l | l
    · exact holdold i l
    · exact cap_compatible_symm (hcapold l i)
    · exact holdC i
    · exact holdouter i l
    · exact hcapold i l
    · exact hcapcap i l
    · exact hcapC i
    · exact hcapouter i l
    · exact cap_compatible_symm (holdC l)
    · exact cap_compatible_symm (hcapC l)
    · exact C.self_transition_mem_piecewiseAffineGroupoid
    · exact hCouter l
    · exact cap_compatible_symm (holdouter l i)
    · exact cap_compatible_symm (hcapouter l i)
    · exact cap_compatible_symm (hCouter i)
    · exact houterouter i l
  let charts : Set (OpenPartialHomeomorph X V3) := range f
  have hmemold (i : ι) : old i ∈ charts := ⟨Sum.inl i, rfl⟩
  have hmemcap (y : S) : cap y ∈ charts := ⟨Sum.inr (Sum.inl y), rfl⟩
  have hmemC : C ∈ charts := ⟨Sum.inr (Sum.inr (Sum.inl ())), rfl⟩
  have hmemouter (l : κ) : outer l ∈ charts := ⟨Sum.inr (Sum.inr (Sum.inr l)), rfl⟩
  have hcharts (c d : charts) : (c : OpenPartialHomeomorph X V3).symm.trans d ∈
      piecewiseAffineGroupoid V3 := by
    obtain ⟨i, hi⟩ := c.property
    obtain ⟨l, hl⟩ := d.property
    simpa only [hi, hl] using hf i l
  refine ⟨charts, ⟨?_, hcharts, hd.closed, ?_⟩, hmemold, hmemouter⟩
  · intro x
    by_cases hxH : x ∈ H
    · by_cases hxD : x ∈ D
      · by_cases hxi : x ∈ interior D
        · exact ⟨⟨C, hmemC⟩, hCs.symm.subset hxi⟩
        · have hxf : x ∈ frontier D := hD.frontier_eq.symm.subset ⟨hxD, hxi⟩
          obtain ⟨y, hy, rfl⟩ := hfront.subset hxf
          exact ⟨⟨cap ⟨y, hy⟩, hmemcap ⟨y, hy⟩⟩, hcpoint ⟨y, hy⟩, hDV hxD⟩
      · let y : Y := ⟨x, holdCover ⟨hxH, hxD⟩⟩
        obtain ⟨i, hi⟩ := hKD.cover y
        exact ⟨⟨old i, hmemold i⟩, (hews i).symm.subset ⟨y, hi, rfl⟩, hxD⟩
    · obtain ⟨l, hl⟩ := hd.cover x
      exact ⟨⟨outer l, hmemouter l⟩, hl, houter hxH⟩
  · intro x hx
    obtain ⟨ell, v, B0, hv, hxB0, hzero, hB0, hhalf⟩ := hd.halfspace x hx
    refine ⟨ell, v, B0.restrOpen O hO, hv, ⟨hxB0, hboundary hx⟩, hzero, ?_, ?_⟩
    · intro c0
      apply pl_transition_mem_of_overlap_cover outer
      · intro y hy
        obtain ⟨l, hl⟩ := hd.cover y
        exact ⟨l, hl, hy.2.2⟩
      · intro l
        exact hcharts ⟨outer l, hmemouter l⟩ c0
      · intro l
        exact cap_restrict_compatible (d l) B0 (hB0 l) hO hO
    · intro y hy
      exact hhalf y hy.1

end PoincareConjecture.M76
