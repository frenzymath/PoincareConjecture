import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Regions.ProtectedDiskCutSide
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.LoopClassTransport
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.exists_protected_cut_filling
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hcut : Y ∩ frontier K = F)
    {g : V2 → X} (hg : ContinuousOn g D) (hgY : MapsTo g D Y)
    (hproper : ∀ z : D, g z ∈ F ↔ (z : V2) ∈ Q)
    (gamma : C(Q, F)) (hrim : ∀ z : Q, g z = (gamma z : X))
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ (d : ι × Y → OpenPartialHomeomorph Y V3) (P : Set Y),
      PLDomain d P ∧
      (P = (Subtype.val : Y → X) ⁻¹' K ∨
        P = (Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) ∧
      frontier P = (Subtype.val : Y → X) ⁻¹' F ∧
      (∀ k, MapsTo (Subtype.val : Y → X) (d k).source (e k.1).source) ∧
      (∀ k, (d k : Y → V3) = (e k.1) ∘ Subtype.val) ∧
      ∃ (f : C(D, P)) (rim : C(Q, ((Subtype.val : Y → X) ⁻¹' F))),
        (∀ z : D, ((f z : Y) : X) = g z) ∧
        (∀ z : Q, ((rim z : Y) : X) = (gamma z : X)) ∧
        (∀ z : Q, (f ⟨z, sphere_subset_closedBall z.property⟩ : Y) = (rim z : Y)) ∧
        (∀ z : D, (f z : Y) ∈ frontier P ↔ (z : V2) ∈ Q) ∧
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map rim.continuous)) ≠ 1 := by
  obtain ⟨d, hplus, hminus, hsource, _, hval, _, hfplus, hfminus, _⟩ :=
    exists_original_PL_cut_domains hK hY hcut
  let G : C(D, Y) := ⟨fun z => ⟨g z, hgY z.property⟩,
    hg.domRestrict.subtype_mk _⟩
  have hside : ∃ P : Set Y, PLDomain d P ∧
      (P = (Subtype.val : Y → X) ⁻¹' K ∨
        P = (Subtype.val : Y → X) ⁻¹' (interior K)ᶜ) ∧
      frontier P = (Subtype.val : Y → X) ⁻¹' F ∧ ∀ z : D, G z ∈ P := by
    rcases hK.protected_disk_lies_on_one_side hcut hg hgY hproper with hp | hm
    · exact ⟨_, hplus, Or.inl rfl, hfplus, fun z => hp.1 z.property⟩
    · exact ⟨_, hminus, Or.inr rfl, hfminus, fun z => hm.1 z.property⟩
  obtain ⟨P, hP, hPside, hPfront, hGP⟩ := hside
  let f : C(D, P) := ⟨fun z => ⟨G z, hGP z⟩, G.continuous.subtype_mk _⟩
  have hFY : F ⊆ Y := hcut.symm.subset.trans inter_subset_left
  let rim : C(Q, ((Subtype.val : Y → X) ⁻¹' F)) :=
    ⟨fun z => ⟨⟨gamma z, hFY (gamma z).property⟩, (gamma z).property⟩,
      ((continuous_subtype_val.comp gamma.continuous).subtype_mk _).subtype_mk _⟩
  have hrange : F ⊆ range (Subtype.val : Y → X) := by
    simpa only [Subtype.range_coe] using hFY
  let H : ((Subtype.val : Y → X) ⁻¹' F) ≃ₜ F :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hrange
  have hpath : (Dehn.squareRimLoop.map rim.continuous).map H.continuous =
      Dehn.squareRimLoop.map gamma.continuous := by
    ext t
    rfl
  refine ⟨d, P, hP, hPside, hPfront, hsource, hval, f, rim,
    fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro z
    exact Subtype.ext (hrim z)
  · intro z
    rw [hPfront]
    exact hproper z
  · intro h
    have hh := (H.loopClass_map_eq_one_iff (Dehn.squareRimLoop.map rim.continuous)).mpr h
    rw [hpath] at hh
    exact hessential hh

end PoincareConjecture.M76
