import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMiddleBall
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)
local notation "J" => Icc (-1 : ℝ) 1
local notation "Q" => sphere (0 : V2) 1
local notation "M" => (J × closedBall (0 : V2) (3 / 2))

def coreExterior (K : Set W) : Set W := closure (squareBlock \ K)

theorem exists_actual_complement_retraction {B T K : Set W}
    (hB : IsFinitePLBallPair W B (T ∪ squareAttachingDisks))
    (hBL : B ⊆ squareBlock) (hT : IsClosed T)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x)
    (hK : IsCompact K) (hKB : K ⊆ B) (hKT : Disjoint K T)
    (rho : C(coreExterior K, Q))
    (hminus : ∀ (u : Q) (y : coreExterior K),
      (y : W) = (-1, (3 / 2 : ℝ) • (u : V2)) → rho y = u) :
    complementaryRegion B ⊆ coreExterior K ∧
      ∃ r : C(coreExterior K, complementaryRegion B),
        ∀ x : coreExterior K, (x : W) ∈ complementaryRegion B → (r x : W) = x := by
  classical
  have hBclosed := hB.isCompact.isClosed
  have hBreg := hB.closure_interior_of_finrank_eq rfl
  have hBfront := hB.frontier_eq_of_finrank_eq rfl
  obtain ⟨_, _, hEfront⟩ := complementaryRegion_geometry
    hBclosed hBreg hBL hT hBfront hcontact hrims
  have hEclosed : IsClosed (complementaryRegion B) := isClosed_closure
  have hLclosed : IsClosed squareBlock := isClosed_Icc.prod isClosed_closedBall
  have hLreg : closure (interior squareBlock) = squareBlock := by
    rw [squareBlock, interior_prod_eq, interior_Icc,
      interior_closedBall _ (by norm_num), closure_prod_eq,
      closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), closure_ball _ (by norm_num)]
  have houtside : squareBlock \ B ⊆ complementaryRegion B := by
    intro x hx
    have hxcl : x ∈ closure (interior squareBlock) := hLreg.symm ▸ hx.1
    have hxc : x ∈ closure (Bᶜ ∩ interior squareBlock) :=
      hBclosed.isOpen_compl.inter_closure ⟨hx.2, hxcl⟩
    have hsub : Bᶜ ∩ interior squareBlock ⊆ interior squareBlock \ B :=
      fun _ hy => ⟨hy.2, hy.1⟩
    exact closure_mono hsub hxc
  have hE0L : coreExterior K ⊆ squareBlock :=
    closure_minimal sdiff_subset hLclosed
  have hEE0 : complementaryRegion B ⊆ coreExterior K :=
    closure_mono (fun _ hx => ⟨interior_subset hx.1, fun hk => hx.2 (hKB hk)⟩)
  have hTE : T ⊆ complementaryRegion B :=
    fun _ hx => hEclosed.frontier_subset (hEfront.symm ▸ Or.inl hx)
  have hEB : complementaryRegion B ∩ B ⊆ T := by
    have hout : complementaryRegion B ⊆ (interior B)ᶜ :=
      closure_minimal (fun _ hx hy => hx.2 (interior_subset hy)) isOpen_interior.isClosed_compl
    have hiout : interior (complementaryRegion B) ⊆ Bᶜ := by
      have h := interior_mono hout
      rwa [interior_compl, hBreg] at h
    intro x hx
    have hxf : x ∈ frontier (complementaryRegion B) :=
      ⟨subset_closure hx.1, fun hi => hiout hi hx.2⟩
    rcases hEfront ▸ hxf with hxT | hxO
    · exact hxT
    · have hc : x ∈ squareAttachingDisks := hcontact ▸ ⟨hx.2, hxO.1⟩
      have hv : ‖x.2‖ = (3 / 2 : ℝ) :=
        le_antisymm (mem_closedBall_zero_iff.mp hc.2) hxO.2
      have hr : x ∈ squareRims := ⟨hc.1, mem_sphere_zero_iff_norm.mpr hv⟩
      exact (hrims.symm ▸ hr).1
  obtain ⟨phi, _, _, hcap, hlateral⟩ := exists_marked_middle_ball hB tau htau hrims hfix
  let prodModel := Homeomorph.Set.prod J (closedBall (0 : V2) (3 / 2))
  let P : M ≃ₜ B := prodModel.symm.trans phi
  let Kpre : Set M := {x | (P x : W) ∈ K}
  have hKpre : IsCompact Kpre :=
    (hK.isClosed.preimage (continuous_subtype_val.comp P.continuous)).isCompact
  have hKrad (x : M) (hx : x ∈ Kpre) : ‖(x.2 : V2)‖ < (3 / 2 : ℝ) := by
    have hle := mem_closedBall_zero_iff.mp x.2.property
    apply lt_of_le_of_ne hle
    intro heq
    have hxI : (prodModel.symm x : W) ∈ squareInnerAnnulus :=
      ⟨x.1.property, mem_sphere_zero_iff_norm.mpr heq⟩
    have hxT : (P x : W) ∈ T := (hlateral (prodModel.symm x)).mp hxI
    exact Set.disjoint_left.mp hKT hx hxT
  let V : Set M := {x | (P x : W) ∉ coreExterior K}
  have hVK : V ⊆ Kpre := by
    intro x hx
    by_contra hxK
    apply hx
    exact subset_closure ⟨hBL (P x).property, hxK⟩
  have hphys (x : (Vᶜ : Set M)) : (P x : W) ∈ coreExterior K :=
    not_not.mp x.property
  let physical : C(↥(Vᶜ : Set M), coreExterior K) :=
    ⟨fun x => ⟨P x, hphys x⟩,
      ((continuous_subtype_val.comp P.continuous).comp continuous_subtype_val).subtype_mk _⟩
  have hrhoMinus (u : Q) (x : (Vᶜ : Set M))
      (hs : (((x : M).1 : J) : ℝ) = -1)
      (hv : ((x : M).2 : V2) = (3 / 2 : ℝ) • (u : V2)) :
      (rho.comp physical) x = u := by
    apply hminus u (physical x)
    have hc : (prodModel.symm (x : M) : W) ∈ squareAttachingDisks :=
      ⟨by change (((x : M).1 : J) : ℝ) ∈ ({-1, 1} : Set ℝ); simp [hs],
        (x : M).2.property⟩
    have hval := hcap ⟨prodModel.symm (x : M), hc⟩ (prodModel.symm (x : M)).property
    change (P (x : M) : W) = (-1, (3 / 2 : ℝ) • (u : V2))
    exact hval.trans (Prod.ext hs hv)
  obtain ⟨rp, hrp⟩ := exists_marked_product_complement_retraction
    (by norm_num : (0 : ℝ) < 3 / 2) Kpre V hKpre hVK hKrad
      (rho.comp physical) hrhoMinus
  have hnorm (u : Q) : ‖(u : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hnormR (u : Q) : ‖(3 / 2 : ℝ) • (u : V2)‖ = (3 / 2 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
      hnorm, mul_one]
  let inc : C(J × Q, M) :=
    ⟨fun z => (z.1, ⟨(3 / 2 : ℝ) • (z.2 : V2),
      mem_closedBall_zero_iff.mpr (hnormR z.2).le⟩), by fun_prop⟩
  have hlat (z : J × Q) : (P (inc z) : W) ∈ T :=
    (hlateral (prodModel.symm (inc z))).mp
      ⟨z.1.property, mem_sphere_zero_iff_norm.mpr (hnormR z.2)⟩
  let lateral : C(J × Q, complementaryRegion B) :=
    ⟨fun z => ⟨P (inc z), hTE (hlat z)⟩,
      ((continuous_subtype_val.comp P.continuous).comp inc.continuous).subtype_mk _⟩
  let s : Set (coreExterior K) := Subtype.val ⁻¹' complementaryRegion B
  let t : Set (coreExterior K) := Subtype.val ⁻¹' B
  let toB : C(t, B) := ⟨fun x => ⟨((x : coreExterior K) : W), x.property⟩, by fun_prop⟩
  let pull0 : C(t, M) := (⟨P.symm, P.symm.continuous⟩ : C(B, M)).comp toB
  have hpull (x : t) : pull0 x ∈ Vᶜ := by
    change ¬ (P (P.symm (toB x)) : W) ∉ coreExterior K
    rw [P.apply_symm_apply]
    exact not_not.mpr (x : coreExterior K).property
  let pull : C(t, ↥(Vᶜ : Set M)) := ⟨fun x => ⟨pull0 x, hpull x⟩,
    pull0.continuous.subtype_mk _⟩
  let g : C(t, complementaryRegion B) := lateral.comp (rp.comp pull)
  have hgfix (x : t) (hx : ((x : coreExterior K) : W) ∈ complementaryRegion B) :
      (g x : W) = ((x : coreExterior K) : W) := by
    let m : M := pull0 x
    have hmT : (P m : W) ∈ T := by
      change (P (P.symm (toB x)) : W) ∈ T
      rw [P.apply_symm_apply]
      exact hEB ⟨hx, x.property⟩
    have hmI := (hlateral (prodModel.symm m)).mpr hmT
    have hmnorm : ‖(m.2 : V2)‖ = (3 / 2 : ℝ) := mem_sphere_zero_iff_norm.mp hmI.2
    let u : Q := ⟨(3 / 2 : ℝ)⁻¹ • (m.2 : V2), mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_eq_abs, hmnorm]
      norm_num)⟩
    have hRu : (3 / 2 : ℝ) • (u : V2) = (m.2 : V2) := by
      change (3 / 2 : ℝ) • ((3 / 2 : ℝ)⁻¹ • (m.2 : V2)) = (m.2 : V2)
      rw [smul_smul, mul_inv_cancel₀ (by norm_num : (3 / 2 : ℝ) ≠ 0), one_smul]
    have hr := hrp m.1 u (pull x) rfl hRu.symm
    have hinc : inc (m.1, u) = m := Prod.ext rfl (Subtype.ext hRu)
    change (P (inc (rp (pull x))) : W) = ((x : coreExterior K) : W)
    rw [hr, hinc]
    change (P (P.symm (toB x)) : W) = (toB x : W)
    exact congrArg Subtype.val (P.apply_symm_apply (toB x))
  have hcover : s ∪ t = univ := by
    ext x
    apply iff_true_intro
    by_cases hxB : (x : W) ∈ B
    · exact Or.inr hxB
    · exact Or.inl (houtside ⟨hE0L x.property, hxB⟩)
  let f : C(s, complementaryRegion B) :=
    ⟨fun x => ⟨((x : coreExterior K) : W), x.property⟩, by fun_prop⟩
  obtain ⟨r, hleft, _⟩ := glue_closed_cover s t
    (hEclosed.preimage continuous_subtype_val) (hBclosed.preimage continuous_subtype_val)
    hcover f g (by
      intro x hxs hxt
      apply Subtype.ext
      exact (hgfix ⟨x, hxt⟩ hxs).symm)
  refine ⟨hEE0, r, ?_⟩
  intro x hx
  exact congrArg Subtype.val (hleft ⟨x, hx⟩)

end PoincareConjecture.M76.HamiltonIndexOne
