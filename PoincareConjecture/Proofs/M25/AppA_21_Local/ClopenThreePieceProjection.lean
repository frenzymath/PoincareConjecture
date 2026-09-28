import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ThreePieceCircleProjection
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25
open Topology3D













theorem exists_circle_projection_on_clopen_three_piece_union
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (W : TopologicalSpace.Opens M) (hWclosed : IsClosed (W : Set M))
    {eta : ℝ} (heta : 0 < eta)
    (e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : ∀ i : Fin 3,
      (e i).source = univ ×ˢ Ioo (-eta) (1 + eta))
    (hsmooth : ∀ i : Fin 3,
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target)
    (hboundary : ∀ i : Fin 3,
      range (fun q : UnitTwoSphere => e i (q, 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hinter : ∀ i : Fin 3,
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hcover : (⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1)) = (W : Set M)) :
    ∃ projection : W → UnitCircle,
      Continuous projection ∧ Function.Surjective projection ∧
      ContMDiff (𝓡 3) (𝓡 1) ∞ projection ∧
      (∀ b : UnitCircle, ∃ V : Set UnitCircle, IsOpen V ∧ b ∈ V ∧
        ∃ T : OpenPartialHomeomorph W (UnitTwoSphere × UnitCircle),
          T.source = projection ⁻¹' V ∧ T.target = univ ×ˢ V ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ T T.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ T.symm T.target ∧
          ∀ x ∈ T.source, (T x).2 = projection x) ∧
      (∀ i : Fin 3,
        (Subtype.val : W → M) ''
            (projection ⁻¹' {periodCircleParam 3 (i.val : ℝ)}) =
          range (fun q : UnitTwoSphere => e i (q, 0))) := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let C : Set RoundCylinderSpace := univ ×ˢ Icc (0 : ℝ) 1
  have hCs (i : Fin 3) : C ⊆ (e i).source := by
    intro z hz
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith only [hz.2.1, hz.2.2, heta]⟩
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ C := by simp [C]
  have hone (q : UnitTwoSphere) : (q, (1 : ℝ)) ∈ C := by simp [C]
  have hpiece (i : Fin 3) : e i '' C ⊆ (W : Set M) := by
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  let q0 : UnitTwoSphere := Classical.choice inferInstance
  have htarget (i : Fin 3) : (e i).target ⊆ (W : Set M) := by
    have hs : IsConnected (e i).source := by
      rw [hsource i]
      exact isConnected_univ.prod (isConnected_Ioo (by linarith only [heta]))
    have ht : IsConnected (e i).target := by
      rw [← (e i).image_source_eq_target]
      exact hs.image (e i) (e i).continuousOn
    apply ht.isPreconnected.subset_isClopen ⟨hWclosed, W.isOpen⟩
    exact ⟨e i (q0, 0), (e i).map_source (hCs i (hzero q0)),
      hpiece i ⟨(q0, 0), hzero q0, rfl⟩⟩
  let hWne : Nonempty W := ⟨⟨e 0 (q0, 0), hpiece 0 ⟨(q0, 0), hzero q0, rfl⟩⟩⟩
  let r : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace W :=
    fun i => ((e i).symm.subtypeRestr hWne).symm
  have hrs (i : Fin 3) : (r i).source = (e i).source := by
    change ((e i).symm.subtypeRestr hWne).target = (e i).source
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      W.openPartialHomeomorphSubtypeCoe_target]
    exact inter_eq_left.mpr (fun z hz => htarget i ((e i).map_source hz))
  have hrt (i : Fin 3) : (r i).target = (Subtype.val : W → M) ⁻¹' (e i).target :=
    (e i).symm.subtypeRestr_source hWne
  have hval (i : Fin 3) (z : RoundCylinderSpace) (hz : z ∈ (r i).source) :
      (r i z).val = e i z := (e i).symm.subtypeRestr_symm_apply hWne hz
  have hrsource (i : Fin 3) : (r i).source = univ ×ˢ Ioo (-eta) (1 + eta) :=
    (hrs i).trans (hsource i)
  have hrsmooth (i : Fin 3) :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (r i) (r i).source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (r i).symm (r i).target := by
    constructor
    · have hcomp : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
          (Subtype.val ∘ r i) (r i).source :=
        ((hsmooth i).1.mono (fun _ hz => hrs i ▸ hz)).congr (hval i)
      intro z hz
      exact (ContMDiffWithinAt.subtypeVal_comp_iff W (r i) (r i).source z).mp (hcomp z hz)
    · change ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : W => (e i).symm x.val) (r i).target
      exact (hsmooth i).2.comp contMDiff_subtype_val.contMDiffOn
        (fun x hx => hrt i ▸ hx)
  have hclosed (i : Fin 3) :
      (Subtype.val : W → M) '' (r i '' C) = e i '' C := by
    rw [image_image]
    exact image_congr (fun z hz => hval i z ((hrs i).symm ▸ hCs i hz))
  have hlower (i : Fin 3) :
      (Subtype.val : W → M) '' range (fun q : UnitTwoSphere => r i (q, 0)) =
        range (fun q : UnitTwoSphere => e i (q, 0)) := by
    rw [← range_comp]
    exact congrArg Set.range (funext fun q => hval i (q, 0)
      ((hrs i).symm ▸ hCs i (hzero q)))
  have hupper (i : Fin 3) :
      (Subtype.val : W → M) '' range (fun q : UnitTwoSphere => r i (q, 1)) =
        range (fun q : UnitTwoSphere => e i (q, 1)) := by
    rw [← range_comp]
    exact congrArg Set.range (funext fun q => hval i (q, 1)
      ((hrs i).symm ▸ hCs i (hone q)))
  have hrboundary (i : Fin 3) :
      range (fun q : UnitTwoSphere => r i (q, 1)) =
        range (fun q : UnitTwoSphere => r (i + 1) (q, 0)) := by
    apply Set.image_injective.mpr Subtype.val_injective
    rw [hupper i, hlower (i + 1), hboundary i]
  have hrinter (i : Fin 3) :
      (r i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (r (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => r (i + 1) (q, 0)) := by
    apply Set.image_injective.mpr Subtype.val_injective
    rw [image_inter Subtype.val_injective, hclosed i, hclosed (i + 1),
      hinter i, hlower (i + 1)]
  have hrcover : (⋃ i : Fin 3, r i '' (univ ×ˢ Icc (0 : ℝ) 1)) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1) :=
      hcover.symm ▸ x.property
    obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨i, z, hz, ?_⟩
    apply Subtype.ext
    exact (hval i z ((hrs i).symm ▸ hCs i hz)).trans hzx
  obtain ⟨p, hp, hsurj, hsm, hcharts, hseams⟩ :=
    exists_circle_projection_of_three_product_charts heta r hrsource hrsmooth
      hrboundary hrinter hrcover
  refine ⟨p, hp, hsurj, hsm, hcharts, ?_⟩
  intro i
  rw [hseams i]
  exact hlower i

end PoincareConjecture.M25
