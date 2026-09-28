import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.OriginalStripDoubleLocus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.WholeAfterStripRemoval
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalResolutionWordExclusion










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1



theorem OriginalResolutionWordExclusionData.whole_double_components
    {X I : Type*} [TopologicalSpace X]
    {f : V2 → X} {Z : Set X} {base : Z} {H : Subgroup (FundamentalGroup Z base)}
    {c : Bool → P2 → V2} {τ : C3 → X}
    (D : OriginalResolutionWordExclusionData f Z base H c τ (1 / 4))
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i p, p ∈ source → (c i p ∈ Q2 ↔ p.1 = 0 ∨ p.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (U : I → Set V2) (a b : I)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (ha : U a = c false '' arm 0) (hb : U b = c true '' arm 0) :
    (∀ i, U i ⊆ D.A ∪ D.C ∨ Disjoint (U i) (D.A ∪ D.C)) ∧
      (∀ i, U i ⊆ (D.A ∪ D.M) ∪ D.C ∨ Disjoint (U i) ((D.A ∪ D.M) ∪ D.C)) ∧
      (U a ∩ Q2).Nonempty ∧
      ¬ U a ⊆ D.A ∪ D.C ∧ ¬ U a ⊆ (D.A ∪ D.M) ∪ D.C := by
  have hcenters := original_strip_centers_disjoint_exteriors c hci D.s0 D.s1
    (by simpa only [inter_comm] using D.strip0A) D.oppositeA.inter_eq
    (by simpa only [inter_comm] using D.strip0M)
    (by simpa only [inter_comm] using D.strip1M) D.oppositeC.inter_eq
    (by simpa only [inter_comm] using D.strip1C)
  have hstrip : doubleLocusOn f D2 ∩
      ((c false '' source) ∪ (c true '' source)) ⊆ U a ∪ U b := by
    rw [ha, hb]
    exact (original_double_locus_inter_strips c hcS hdisj hτ hfull h0 h1).subset
  have ha' : Disjoint (U a) ((D.A ∪ D.M) ∪ D.C) := ha ▸ hcenters.1
  have hb' : Disjoint (U b) ((D.A ∪ D.M) ∪ D.C) := hb ▸ hcenters.2
  obtain ⟨hwholeU, hwholeV⟩ := whole_components_of_selected_strip_pair U a b
    D.diskA.isCompact.isClosed D.diskM.isCompact.isClosed D.diskC.isCompact.isClosed
    D.disjointAM D.disjointMC D.disjointAC D.cover hcover (fun _ h ↦ h.1)
    hconn hpairwise hstrip ha' hb'
  have hx : c false (0, 0) ∈ U a := by
    rw [ha]
    exact ⟨(0, 0), ⟨by norm_num, rfl⟩, rfl⟩
  have hxQ : c false (0, 0) ∈ Q2 :=
    (hcQ false (0, 0) (by norm_num [source])).mpr (Or.inl rfl)
  have hnotV : ¬ U a ⊆ (D.A ∪ D.M) ∪ D.C :=
    fun h ↦ disjoint_left.mp ha' hx (h hx)
  have hsmall : D.A ∪ D.C ⊆ (D.A ∪ D.M) ∪ D.C := by
    rintro x (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  exact ⟨hwholeU, hwholeV, ⟨_, hx, hxQ⟩, fun h ↦ hnotV (h.trans hsmall), hnotV⟩

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
