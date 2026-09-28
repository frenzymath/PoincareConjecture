import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalAnnularDiskFilling
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.PolygonCircleModels

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1

theorem exists_essential_enclosing_annular_circle
    {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hdepth : ∀ x ∈ P.boundary ℝ, -1 < depth 8 x ∧ depth 8 x < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside) :
    ∃ (gamma : C(Q2,Ann)) (a : V2 → P2),
      Function.Injective gamma ∧ FinitePiecewiseAffineOn a Q2 ∧
      (∀ x : Q2, a x = (gamma x : P2)) ∧
      (∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1) ∧
      Subtype.val '' range gamma = P.boundary ℝ ∧
      (∀ z : Ann, z ∈ range gamma ↔ (z : P2) ∈ P.boundary ℝ) ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  obtain ⟨g,hg⟩ := P.exists_finitePL_square_circle hP hi
  let boundary : C(P.boundary ℝ, Ann) := ⟨fun x =>
    ⟨x,mem_squareAnnulus_iff_depth.mpr
      ⟨(hdepth x x.property).1.le,(hdepth x x.property).2.le⟩⟩,
    continuous_subtype_val.subtype_mk _⟩
  let gamma : C(Q2,Ann) := boundary.comp ⟨g,g.continuous⟩
  have hgi : Function.Injective gamma := by
    intro x y hxy
    apply g.injective
    exact Subtype.ext (congrArg (fun z : Ann => (z : P2)) hxy)
  obtain ⟨a,ha,haval⟩ := hg
  have hval (x : Q2) : a x = (gamma x : P2) := (haval x).symm
  have hgammaDepth (x : Q2) : -1 < depth 8 (gamma x : P2) ∧
      depth 8 (gamma x : P2) < 1 := hdepth (g x) (g x).property
  have hrange (z : Ann) : z ∈ range gamma ↔ (z : P2) ∈ P.boundary ℝ := by
    constructor
    · rintro ⟨x,rfl⟩
      exact (g x).property
    · intro hz
      let w : P.boundary ℝ := ⟨z,hz⟩
      refine ⟨g.symm w,?_⟩
      apply Subtype.ext
      change (g (g.symm w) : P2) = (z : P2)
      exact congrArg Subtype.val (g.apply_symm_apply w)
  have hfull : Subtype.val '' range gamma = P.boundary ℝ := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hrange w).mp hw
    · intro hz
      let w : Ann := ⟨z,mem_squareAnnulus_iff_depth.mpr
        ⟨(hdepth z hz).1.le,(hdepth z hz).2.le⟩⟩
      exact ⟨w,(hrange w).mpr hz,rfl⟩
  refine ⟨gamma,a,hgi,ha,hval,hgammaDepth,hfull,hrange,?_⟩
  intro hnull
  have hgammaNull := Dehn.nullhomotopic_of_squareRimLoop gamma
    (Path.Homotopic.Quotient.eq.mp hnull)
  have hcomp : gamma.comp ⟨g.symm,g.symm.continuous⟩ = boundary := by
    apply ContinuousMap.ext
    intro x
    change boundary (g (g.symm x)) = boundary x
    rw [g.apply_symm_apply]
  have hbNull : boundary.Nullhomotopic :=
    hcomp ▸ hgammaNull.comp_left ⟨g.symm,g.symm.continuous⟩
  obtain ⟨_,hinside⟩ := Dehn.Annuli.polygon_disk_in_essential_annulus_of_null_boundary
    (ContinuousMap.id Ann) standard_annulus_lower_rim_not_nullhomotopic
    P hP hi hdepth boundary (fun _ => rfl) hbNull
  have hpoint : (1,1) ∈ Dehn.annulusSquare 8 1 := by
    change (1 ≤ (1 : ℝ) ∧ 1 ≤ 8-1) ∧ (1 ≤ (1 : ℝ) ∧ 1 ≤ 8-1)
    norm_num
  have hlt := (hinside (subset_closure (hencl hpoint))).2
  exact (not_lt_of_ge ((_root_.Dehn.mem_annulusSquare_iff 8 1 (1,1)).mp hpoint)) hlt

end PoincareConjecture.M76
