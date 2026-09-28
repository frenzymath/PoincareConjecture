import PoincareConjecture.Proofs.M76.Mathlib.CoveringPLAtlas
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralImageOpenDeformation
import PoincareConjecture.Proofs.M76.Mathlib.HomotopyConnectedRange
import Mathlib.Topology.Homotopy.Lifting










set_option autoImplicit false

open Set Geometry unitInterval

namespace IsCoveringMap





theorem exists_polyhedralPL_lift
    {D E M X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [TopologicalSpace X]
    {p : X → M} (hp : IsCoveringMap p)
    {c : ι → OpenPartialHomeomorph M E}
    (d : ι × X → OpenPartialHomeomorph X E)
    (hcenter : ∀ i x, p x ∈ (c i).source → x ∈ (d (i, x)).source)
    (hval : ∀ k, EqOn (d k) ((c k.1) ∘ p) (d k).source)
    (S : SimplicialComplex ℝ D) (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    {f : D → M} (hf : PolyhedralPLInCharts c f S.space)
    (v0 : S.space) (x0 : X) (hx0 : p x0 = f v0) :
    ∃ g : D → X, g v0 = x0 ∧ EqOn (p ∘ g) f S.space ∧
      PolyhedralPLInCharts d g S.space := by
  classical
  let F : C(S.space, M) := ⟨fun x => f x, hf.continuousOn.domRestrict⟩
  obtain ⟨G, ⟨hG0, hpG⟩, _⟩ := hp.existsUnique_continuousMap_lifts F v0 x0 hx0
  let g : D → X := fun x => if hx : x ∈ S.space then G ⟨x, hx⟩ else x0
  have hg (x : S.space) : g x = G x := by simp only [g, dif_pos x.property]
  have hgc : ContinuousOn g S.space := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact G.continuous.congr (fun x => (hg x).symm)
  have hpg : EqOn (p ∘ g) f S.space := by
    intro x hx
    change p (g x) = f x
    rw [hg ⟨x, hx⟩]
    exact congrFun hpG ⟨x, hx⟩
  exact ⟨g, (hg v0).trans hG0, hpg, hf.lift d hcenter hval S hS hgc hpg⟩






theorem exists_polyhedralPL_open_successor
    {D E M X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X]
    {p : X → M} (hp : IsCoveringMap p)
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (S : SimplicialComplex ℝ D) (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    {f : D → M} (hf : PolyhedralPLInCharts e f S.space)
    (v0 : S.space) (x0 : X) (hx0 : p x0 = f v0)
    {W : Set M} (hW : IsOpen W) (hfW : MapsTo f S.space W)
    {r : M → ℝ} (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) :
    ∃ (d : ι × X → OpenPartialHomeomorph X E) (g : D → X),
      (∀ x, ∃ k, x ∈ (d k).source) ∧
      (∀ k l, (d k).symm.trans (d l) ∈ piecewiseAffineGroupoid E) ∧
      (∀ k, (d k : X → E) = (e k.1) ∘ p) ∧
      (∀ k, LocallyPiecewiseAffineOn ((r ∘ p) ∘ (d k).symm) (d k).target) ∧
      g v0 = x0 ∧ EqOn (p ∘ g) f S.space ∧ PolyhedralPLInCharts d g S.space ∧
      ∃ (z : X → ℝ) (Q : Set X), IsCompact Q ∧ Q ⊆ p ⁻¹' W ∧
        Continuous z ∧ (∀ x, x ∉ Q → z x = 0) ∧
        (∀ k, LocallyPiecewiseAffineOn (z ∘ (d k).symm) (d k).target) ∧
        (∀ x ∈ g '' S.space, z x = 1) ∧
        ∀ c : ℝ, 0 < c → c < 1 →
          let P : Set X := {x | c ≤ z x}
          let O : Set X := {x | c < z x}
          IsCompact P ∧ IsOpen O ∧ PathConnectedSpace O ∧
            g '' S.space ⊆ O ∧ O ⊆ P ∧ P ⊆ p ⁻¹' W ∧
            ∃ (a : C(O, O))
              (H : (ContinuousMap.id O).HomotopyRel a {x : O | (x : X) ∈ g '' S.space}),
              range a = {x : O | (x : X) ∈ g '' S.space} ∧
              (∀ (t : I) (x : O), 0 ≤ r (p x) → 0 ≤ r (p (H (t, x)))) ∧
              (∀ (t : I) (x : O), r (p x) = 0 → r (p (H (t, x))) = 0) ∧
              ∀ (t : I) (x : O), z (H (t, x)) =
                (1 - (t : ℝ)) * z x + (t : ℝ) := by
  obtain ⟨d, hdcover, hdcenter, _, hdtarget, hdval, hdinv, hdcompat⟩ :=
    hp.isLocalHomeomorph.exists_piecewiseAffine_coordinate_cover_over e hcover hcompat
  obtain ⟨g, hg0, hpg, hg⟩ := hp.exists_polyhedralPL_lift d
    (fun i x => (hdcenter i x).mpr)
    (fun k x _ => congrFun (hdval k) x) S hS hf v0 x0 hx0
  have hrUp : ∀ k, LocallyPiecewiseAffineOn ((r ∘ p) ∘ (d k).symm) (d k).target := by
    intro k
    apply ((hrPL k.1).mono (d k).open_target (hdtarget k)).congr
    intro y hy
    exact congrArg r (hdinv k hy).symm
  have hgW : MapsTo g S.space (p ⁻¹' W) := by
    intro x hx
    change (p ∘ g) x ∈ W
    rw [hpg hx]
    exact hfW hx
  obtain ⟨z, Q, hQ, hQW, hz, hzoff, hzPL, hzA, hlevel⟩ :=
    OpenPartialHomeomorph.exists_polyhedral_image_open_cut_deformation d hdcompat hdcover
      S hS hg (hW.preimage hp.continuous) hgW (hr.comp hp.continuous) hrUp
  have hA : IsPathConnected (g '' S.space) := by
    have h := isPathConnected_range hg.continuousOn.domRestrict
    simpa only [range_domRestrict] using h
  refine ⟨d, g, hdcover, hdcompat, hdval, hrUp, hg0, hpg, hg,
    z, Q, hQ, hQW, hz, hzoff, hzPL, hzA, ?_⟩
  intro c hc hc1
  obtain ⟨hP, hO, hAO, hOP, hPW, a, H, ha, hpos, hzero, hmass⟩ := hlevel c hc hc1
  have hconn : PathConnectedSpace {x : X | c < z x} := by
    apply H.toHomotopy.pathConnectedSpace_of_range
    rw [ha]
    exact hA.preimage_coe hAO
  exact ⟨hP, hO, hconn, hAO, hOP, hPW, a, H, ha, hpos, hzero, hmass⟩

end IsCoveringMap
