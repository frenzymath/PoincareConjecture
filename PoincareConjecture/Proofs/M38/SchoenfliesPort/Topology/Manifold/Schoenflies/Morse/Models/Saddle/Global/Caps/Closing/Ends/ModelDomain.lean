import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelCriticalCount
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.LowerSide
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.DiskSublevels







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem terminal_model_critical_height_location
    (data : TerminalSaddleData M P p e) {y : S2}
    (hy : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel q)) y = 0) :
    inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel y) ∈
        Ioo data.ends.lowerCut data.ends.upperCut ∨
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel y) ∉
        data.toTerminalSaddleGeometry.I := by
  classical
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  let Z := {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0}
  obtain ⟨q₀, h₀, hc₀⟩ :=
    exists_critical_in_terminal_model_band_interior data.toTerminalSaddleGeometry
  choose q hqK hqout hqc using exists_critical_in_terminal_model_cap data
  have hne (j : Fin 3) : q₀ ≠ q j := by
    intro he
    exact hqout j (he ▸ ⟨h₀.1.le, h₀.2.le⟩)
  let J : Option (Fin 3) → Z
    | none => ⟨q₀, hc₀⟩
    | some j => ⟨q j, hqc j⟩
  have hJ : Injective J := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some k => exact (hne k (congrArg Subtype.val hab)).elim
    | some j =>
      cases b with
      | none => exact (hne j (congrArg Subtype.val hab).symm).elim
      | some k =>
        have he : q j = q k := congrArg Subtype.val hab
        by_cases hjk : j = k
        · exact congrArg some hjk
        · exact (disjoint_left.mp (data.model_disjoint hjk)
            ⟨q j, hqK j, rfl⟩ ⟨q j, he ▸ hqK k, rfl⟩).elim
  let : Finite Z := (finite_terminal_model_critical_points data).1
  let : Fintype Z := Fintype.ofFinite Z
  have hcard : Fintype.card Z ≤ 4 := by
    simpa only [Nat.card_eq_fintype_card] using
      (finite_terminal_model_critical_points data).2
  have hsurj : Surjective J :=
    ((Fintype.bijective_iff_injective_and_card J).mpr ⟨hJ, by
      have hle := Fintype.card_le_of_injective J hJ
      simp only [Fintype.card_option, Fintype.card_fin] at hle ⊢
      omega⟩).2
  obtain ⟨a, ha⟩ := hsurj ⟨y, hy⟩
  cases a with
  | none =>
    have he : q₀ = y := congrArg Subtype.val ha
    exact Or.inl (he ▸ h₀)
  | some j =>
    have he : q j = y := congrArg Subtype.val ha
    exact Or.inr (he ▸ hqout j)


theorem terminal_model_cut_regular
    (data : TerminalSaddleData M P p e) (q : S2)
    (hq : inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
        data.ends.lowerCut ∨
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
        data.ends.upperCut) :
    mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q ≠ 0 := by
  have hab : data.ends.lowerCut < data.ends.upperCut := by
    rw [data.lowerCut_eq, data.upperCut_eq]
    linarith [data.eta_pos]
  intro hc
  rcases terminal_model_critical_height_location data hc with hin | hout
  · rcases hq with hq | hq
    · rw [hq] at hin
      exact lt_irrefl _ hin.1
    · rw [hq] at hin
      exact lt_irrefl _ hin.2
  · apply hout
    change _ ∈ Icc _ _
    rcases hq with hq | hq <;> rw [hq]
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩

private theorem outside_component_eq_strict_sublevel
    {h : S2 → Real} (hh : Continuous h) {a b : Real} (hab : a ≤ b)
    {q : S2} (hq : h q < a) :
    connectedComponentIn {x | h x ∉ Icc a b} q =
      connectedComponentIn (h ⁻¹' Iio a) q := by
  have hqO : q ∈ {x | h x ∉ Icc a b} := fun hx => hq.not_ge hx.1
  have hsub : connectedComponentIn {x | h x ∉ Icc a b} q ⊆ h ⁻¹' Iio a := by
    intro x hx
    have hconn : IsPreconnected (connectedComponentIn {x | h x ∉ Icc a b} q) :=
      isPreconnected_connectedComponentIn
    exact hconn.gt_of_ne hh.continuousOn
      (fun y hy he => (connectedComponentIn_subset {x | h x ∉ Icc a b} q hy)
        (he ▸ ⟨le_rfl, hab⟩))
      ⟨q, mem_connectedComponentIn hqO, hq⟩ hx
  apply subset_antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hqO) hsub
  · apply connectedComponentIn_mono
    exact fun x hx hi => hx.not_ge hi.1

private theorem closure_strict_component_eq_closed_component
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a : Real} {q : S2} (hq : h q < a)
    (hreg : ∀ x, h x = a → mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0) :
    closure (connectedComponentIn (h ⁻¹' Iio a) q) =
      connectedComponentIn (h ⁻¹' Iic a) q := by
  let : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2
  have heq := Poincare.Topology.connectedComponentIn_sublevel_eq_closure_strict_sublevel
    (O := univ) isOpen_univ hh.continuous.continuousOn (mem_univ q) hq
    (subset_univ _) (fun x _ hxa => Or.inr (by
      simpa only [hxa] using
        Poincare.Geometry.Manifold.hasConnectedLowerSide_of_regular hh isOpen_univ
          (mem_univ x) (hreg x hxa)))
  simpa only [univ_inter] using heq.symm



theorem terminal_model_domain_component
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let h : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    (h (data.modelSeed i) < data.ends.lowerCut ∧
      data.toTerminalSaddleGeometry.modelDomain i =
        connectedComponentIn (h ⁻¹' Iic data.ends.lowerCut) (data.modelSeed i)) ∨
    (data.ends.upperCut < h (data.modelSeed i) ∧
      data.toTerminalSaddleGeometry.modelDomain i =
        connectedComponentIn (h ⁻¹' Ici data.ends.upperCut) (data.modelSeed i)) := by
  dsimp only
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp contMDiff_coe_sphere)
  have hab : data.ends.lowerCut ≤ data.ends.upperCut := by
    rw [data.lowerCut_eq, data.upperCut_eq]
    linarith [data.eta_pos]
  have hseed : h (data.modelSeed i) < data.ends.lowerCut ∨
      data.ends.upperCut < h (data.modelSeed i) := by
    have hs := data.modelSeed_outside i
    change ¬ (data.ends.lowerCut ≤ h (data.modelSeed i) ∧
      h (data.modelSeed i) ≤ data.ends.upperCut) at hs
    simpa only [not_and_or, not_le] using hs
  rcases hseed with hlo | hhi
  · refine Or.inl ⟨hlo, ?_⟩
    change closure (connectedComponentIn {x | h x ∉ Icc _ _} _) = _
    rw [outside_component_eq_strict_sublevel hh.continuous hab hlo]
    exact closure_strict_component_eq_closed_component hh hlo
      (fun x hx => terminal_model_cut_regular data x (Or.inl hx))
  · refine Or.inr ⟨hhi, ?_⟩
    have hneg : {x : S2 | h x ∉ Icc data.ends.lowerCut data.ends.upperCut} =
        {x | (-h) x ∉ Icc (-data.ends.upperCut) (-data.ends.lowerCut)} := by
      ext x
      simp only [Pi.neg_apply, mem_ofPred_eq, mem_Icc, neg_le_neg_iff, and_comm]
    change closure (connectedComponentIn {x | h x ∉ Icc _ _} _) = _
    rw [hneg]
    have hcomp := outside_component_eq_strict_sublevel (h := -h) hh.neg.continuous
      (neg_le_neg hab) (neg_lt_neg hhi)
    rw [hcomp]
    have heq := closure_strict_component_eq_closed_component (h := -h) hh.neg (neg_lt_neg hhi)
      (fun x hx => by
        have hc := terminal_model_cut_regular data x (Or.inr (neg_injective hx))
        change mfderiv (𝓡 2) 𝓘(Real, Real) h x ≠ 0 at hc
        rw [mfderiv_neg]
        exact neg_ne_zero.mpr hc)
    simpa only [preimage, mem_Iic, mem_Ici, Pi.neg_apply, neg_le_neg_iff, h] using heq

private theorem height_eq_on_frontier_of_closed_sublevel_component
    {h : S2 → Real} (hh : Continuous h) {K : Set S2} (hK : IsClosed K)
    {a : Real} {p : S2} (hcomp : K = connectedComponentIn (h ⁻¹' Iic a) p)
    {q : S2} (hq : q ∈ frontier K) : h q = a := by
  let : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2
  have hqK : q ∈ K := hK.closure_eq ▸ hq.1
  have hqc : q ∈ connectedComponentIn (h ⁻¹' Iic a) p := hcomp ▸ hqK
  have hle : h q ≤ a := connectedComponentIn_subset (h ⁻¹' Iic a) p hqc
  apply le_antisymm hle
  by_contra hnot
  have hlt : h q < a := lt_of_not_ge hnot
  have hbase : h ⁻¹' Iic a ∈ 𝓝 q := Filter.mem_of_superset
    ((isOpen_Iio.preimage hh).mem_nhds hlt) (preimage_mono Iio_subset_Iic_self)
  have hnhds := connectedComponentIn_mem_nhds hbase
  rw [← connectedComponentIn_eq hqc, ← hcomp] at hnhds
  exact hq.2 (mem_interior_iff_mem_nhds.mpr hnhds)



theorem terminal_model_domain_boundary
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let h : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    (h (data.modelSeed i) < data.ends.lowerCut ∧
      ∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = data.ends.lowerCut) ∨
    (data.ends.upperCut < h (data.modelSeed i) ∧
      ∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = data.ends.upperCut) := by
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  have hh : Continuous h :=
    (innerSL Real (M.v : E3)).continuous.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous.comp continuous_subtype_val)
  have hfront (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      data.modelDisk i x ∈ frontier (data.toTerminalSaddleGeometry.modelDomain i) := by
    rw [← data.modelDisk_image,
      ← (data.modelDisk i).image_sphere_eq_frontier (data.modelDisk_source i) rfl]
    exact mem_image_of_mem _ hx
  rcases terminal_model_domain_component data i with ⟨hlo, heq⟩ | ⟨hhi, heq⟩
  · refine Or.inl ⟨hlo, fun x hx => ?_⟩
    exact height_eq_on_frontier_of_closed_sublevel_component hh isClosed_closure heq (hfront x hx)
  · refine Or.inr ⟨hhi, fun x hx => ?_⟩
    have heq' : data.toTerminalSaddleGeometry.modelDomain i =
        connectedComponentIn ((-h) ⁻¹' Iic (-data.ends.upperCut)) (data.modelSeed i) := by
      simpa only [preimage, mem_Iic, mem_Ici, Pi.neg_apply, neg_le_neg_iff, h] using heq
    exact neg_injective (height_eq_on_frontier_of_closed_sublevel_component hh.neg
      isClosed_closure heq' (hfront x hx))



theorem terminal_model_domain_extremum
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let h : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    ∃ q ∈ data.toTerminalSaddleGeometry.modelDomain i,
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 ∧
      ((h q < data.ends.lowerCut ∧ IsLocalMin h q ∧
          (∀ x ∈ data.toTerminalSaddleGeometry.modelDomain i,
            h q ≤ h x ∧ h x ≤ data.ends.lowerCut) ∧
          (∀ x ∈ data.toTerminalSaddleGeometry.modelDomain i, x ≠ q → h q < h x) ∧
          (∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = data.ends.lowerCut)) ∨
        (data.ends.upperCut < h q ∧ IsLocalMax h q ∧
          (∀ x ∈ data.toTerminalSaddleGeometry.modelDomain i,
            data.ends.upperCut ≤ h x ∧ h x ≤ h q) ∧
          (∀ x ∈ data.toTerminalSaddleGeometry.modelDomain i, x ≠ q → h x < h q) ∧
          (∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = data.ends.upperCut))) := by
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp contMDiff_coe_sphere)
  obtain ⟨q, hqK, hqout, hqc⟩ := exists_critical_in_terminal_model_cap data i
  have huniq : ∀ x ∈ data.modelDisk i '' closedBall (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) h x = 0 → x = q := by
    obtain ⟨r, hr, hru⟩ := existsUnique_critical_in_terminal_model_cap data i
    intro x hx hxc
    exact (hru x ⟨data.modelDisk_image i ▸ hx, hxc⟩).trans (hru q ⟨hqK, hqc⟩).symm
  have hqD : q ∈ data.modelDisk i '' closedBall (0 : E2) 1 := data.modelDisk_image i ▸ hqK
  have hab : data.ends.lowerCut ≤ data.ends.upperCut := by
    rw [data.lowerCut_eq, data.upperCut_eq]
    linarith [data.eta_pos]
  refine ⟨q, hqK, hqc, ?_⟩
  rcases terminal_model_domain_boundary data i with ⟨hlo, hboundary⟩ | ⟨hhi, hboundary⟩
  · have heq := (terminal_model_domain_component data i).resolve_right
      (fun hupper => (not_lt_of_ge (hlo.le.trans hab)) hupper.1)
    have hle : h q ≤ data.ends.lowerCut :=
      connectedComponentIn_subset (h ⁻¹' Iic data.ends.lowerCut) (data.modelSeed i) (heq.2 ▸ hqK)
    have hlt : h q < data.ends.lowerCut := by
      apply lt_of_le_of_ne hle
      intro he
      exact hqout ⟨he.ge, hle.trans hab⟩
    obtain ⟨hmin, hbounds, hstrict, _⟩ := height_bounds_on_disk_of_unique_critical hh
      (data.modelDisk i) (data.modelDisk_source i) hqD hlt hboundary huniq
    refine Or.inl ⟨hlt, hmin, ?_, ?_, hboundary⟩
    · simpa only [data.modelDisk_image] using hbounds
    · simpa only [data.modelDisk_image] using hstrict
  · have heq := (terminal_model_domain_component data i).resolve_left
      (fun hlower => (not_lt_of_ge (hab.trans hhi.le)) hlower.1)
    have hle : data.ends.upperCut ≤ h q :=
      connectedComponentIn_subset (h ⁻¹' Ici data.ends.upperCut) (data.modelSeed i) (heq.2 ▸ hqK)
    have hlt : data.ends.upperCut < h q := by
      apply lt_of_le_of_ne hle
      intro he
      exact hqout ⟨hab.trans hle, he.ge⟩
    have huniqn : ∀ x ∈ data.modelDisk i '' closedBall (0 : E2) 1,
        mfderiv (𝓡 2) 𝓘(Real, Real) (-h) x = 0 → x = q := by
      intro x hx hxc
      exact huniq x hx (by simpa only [mfderiv_neg, neg_eq_zero] using hxc)
    obtain ⟨hmin, hbounds, hstrict, _⟩ := height_bounds_on_disk_of_unique_critical hh.neg
      (data.modelDisk i) (data.modelDisk_source i) hqD (neg_lt_neg hlt)
      (fun x hx => congrArg Neg.neg (hboundary x hx)) huniqn
    refine Or.inr ⟨hlt, ?_, ?_, ?_, hboundary⟩
    · simpa only [neg_neg] using hmin.neg
    · intro x hx
      have hb := hbounds x (data.modelDisk_image i ▸ hx)
      exact ⟨neg_le_neg_iff.mp hb.2, neg_le_neg_iff.mp hb.1⟩
    · intro x hx hxq
      exact neg_lt_neg_iff.mp (hstrict x (data.modelDisk_image i ▸ hx) hxq)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
