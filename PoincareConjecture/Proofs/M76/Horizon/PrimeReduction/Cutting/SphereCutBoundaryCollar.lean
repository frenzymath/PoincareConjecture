import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarStrips
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1
local notation "I" => Icc (0 : ℝ) 1

private theorem isOpen_collar_subinterval
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : Set E} {c : E × ℝ → X}
    (hc : Topology.IsEmbedding (fun z : (A ×ˢ J : Set (E × ℝ)) => c z))
    {δ a b : ℝ} (hδ : δ ≤ 1)
    (ho : IsOpen (c '' (A ×ˢ Ioo (-δ) δ)))
    (hab : Ioo a b ⊆ Ioo (-δ) δ) : IsOpen (c '' (A ×ˢ Ioo a b)) := by
  let f : (A ×ˢ J : Set (E × ℝ)) → X := fun z => c z
  let V : Set (A ×ˢ J : Set (E × ℝ)) := {z | (z : E × ℝ).2 ∈ Ioo a b}
  have hV : IsOpen V := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
  have hfull : Ioo (-δ) δ ⊆ J := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  have himage : f '' V = c '' (A ×ˢ Ioo a b) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, hz⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, ⟨hz.1, hfull (hab hz.2)⟩⟩, hz.2, rfl⟩
  rw [← himage]
  apply hc.isInducing.isOpen_image_of_subset_open hV ho
  · rw [himage]
    exact image_mono (prod_mono subset_rfl hab)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, ⟨hz.1, hfull hz.2⟩⟩, rfl⟩

theorem exists_sphere_cut_boundary_collars
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hcPL : PolyhedralPLInCharts e c (N.space ×ˢ J))
    (hc : Topology.IsEmbedding (fun z : (N.space ×ˢ J : Set (E × ℝ)) => c z))
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ ≤ 1)
    (hinside : MapsTo c (N.space ×ˢ Icc (-δ) δ) (interior R))
    (hopen : IsOpen (c '' (N.space ×ˢ Ioo (-δ) δ))) :
    ∃ d : Bool → E × ℝ → X,
      (∀ b x r, d b (x, r) = c (x, if b then ε + (δ - ε) * r else -(ε + (δ - ε) * r))) ∧
      let Q := R \ c '' (N.space ×ˢ Ioo (-ε) ε)
      ∀ b, PolyhedralPLInCharts e (d b) (N.space ×ˢ I) ∧
        Topology.IsEmbedding (fun z : (N.space ×ˢ I : Set (E × ℝ)) => d b z) ∧
        MapsTo (d b) (N.space ×ˢ I) Q ∧
        (∀ x, d b (x, 0) = c (x, if b then ε else -ε)) ∧
        (∀ z ∈ N.space ×ˢ I,
          d b z ∈ c '' (N.space ×ˢ ({if b then ε else -ε} : Set ℝ)) ↔ z.2 = 0) ∧
        ∀ η : ℝ, 0 < η → η < 1 →
          IsOpen ((Subtype.val : Q → X) ⁻¹' (d b '' (N.space ×ˢ Ico 0 η))) := by
  classical
  let time : Bool → ℝ → ℝ := fun b r => if b then ε + (δ - ε) * r else -(ε + (δ - ε) * r)
  let shift : Bool → (E × ℝ →ᴬ[ℝ] E × ℝ) := fun b =>
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (if b then ContinuousAffineMap.const ℝ (E × ℝ) ε +
        (δ - ε) • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
      else -(ContinuousAffineMap.const ℝ (E × ℝ) ε +
        (δ - ε) • (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap))
  have hshift (b : Bool) (z : E × ℝ) : shift b z = (z.1, time b z.2) := by
    cases b <;> rfl
  have hwidth : 0 < δ - ε := sub_pos.mpr hεδ
  have htime (b : Bool) {r : ℝ} (hr : r ∈ I) :
      time b r ∈ Icc (-δ) δ := by
    have hlo : ε ≤ ε + (δ - ε) * r := by nlinarith [hr.1]
    have hhi : ε + (δ - ε) * r ≤ δ := by nlinarith [hr.2]
    cases b <;> dsimp [time] <;> constructor <;> linarith
  have hfull : N.space ×ˢ Icc (-δ) δ ⊆ N.space ×ˢ J := by
    rintro ⟨x, r⟩ ⟨hx, hr⟩
    exact ⟨hx, by constructor <;> linarith [hr.1, hr.2]⟩
  have hmap (b : Bool) : MapsTo (shift b) (N.space ×ˢ I) (N.space ×ˢ J) := by
    intro z hz
    rw [hshift]
    exact hfull ⟨hz.1, htime b hz.2⟩
  have hci : InjOn c (N.space ×ˢ J) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hc.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) heq)
  have hshiftinj (b : Bool) : Function.Injective (shift b) := by
    intro x y hxy
    rw [hshift, hshift] at hxy
    have hfst := congrArg Prod.fst hxy
    have hsnd := congrArg Prod.snd hxy
    dsimp only at hfst hsnd
    apply Prod.ext hfst
    cases b <;> dsimp [time] at hsnd <;> nlinarith
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨KI, hKI, hKIs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨L, hL, hLs, _⟩ := N.exists_finite_triangulation_prod KI hN hKI
  rw [hKIs] at hLs
  let d : Bool → E × ℝ → X := fun b => c ∘ shift b
  let Q := R \ c '' (N.space ×ˢ Ioo (-ε) ε)
  refine ⟨d, ?_, ?_⟩
  · intro b x r
    exact congrArg c (hshift b (x, r))
  dsimp only
  intro b
  have hdPL : PolyhedralPLInCharts e (d b) (N.space ×ˢ I) := by
    have hf : FinitePiecewiseAffineOn (shift b) L.space :=
      ⟨L, hL, rfl, L.affineOnFaces_affine (shift b)⟩
    have h := hcPL.comp_finitePiecewiseAffineOn L hL hf (hLs.symm ▸ hmap b)
    exact hLs ▸ h
  have hdi : InjOn (d b) (N.space ×ˢ I) := by
    intro x hx y hy hxy
    exact hshiftinj b (hci (hmap b hx) (hmap b hy) hxy)
  have hdembedding : Topology.IsEmbedding (fun z : (N.space ×ˢ I : Set (E × ℝ)) => d b z) := by
    let : CompactSpace (N.space ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((N.isCompact_space_of_finite hN).prod isCompact_Icc)
    exact (hdPL.continuousOn.domRestrict.isClosedEmbedding
      (fun x y h => Subtype.ext (hdi x.property y.property h))).isEmbedding
  have hdvalue (z : E × ℝ) : d b z = c (z.1, time b z.2) := congrArg c (hshift b z)
  have hdQ : MapsTo (d b) (N.space ×ˢ I) Q := by
    intro z hz
    rw [hdvalue]
    refine ⟨interior_subset (hinside ⟨hz.1, htime b hz.2⟩), ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwJ : w ∈ N.space ×ˢ J := by
      exact ⟨hw.1, by constructor <;> linarith [hw.2.1, hw.2.2]⟩
    have hzJ : (z.1, time b z.2) ∈ N.space ×ˢ J :=
      hfull ⟨hz.1, htime b hz.2⟩
    have hpair : w = (z.1, time b z.2) := hci hwJ hzJ heq
    have ht := congrArg Prod.snd hpair
    dsimp only at ht
    cases b <;> dsimp [time] at ht <;> nlinarith [hz.2.1, hw.2.1, hw.2.2]
  have hdbase (x : E) : d b (x, 0) = c (x, if b then ε else -ε) := by
    rw [hdvalue]
    cases b <;> simp [time]
  have hdzero (z : E × ℝ) (hz : z ∈ N.space ×ˢ I) :
      d b z ∈ c '' (N.space ×ˢ ({if b then ε else -ε} : Set ℝ)) ↔ z.2 = 0 := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwt : w.2 = if b then ε else -ε := hw.2
      have hwJ : w ∈ N.space ×ˢ J := by
        refine ⟨hw.1, ?_⟩
        rw [hwt]
        cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
      rw [hdvalue] at heq
      have hzJ : (z.1, time b z.2) ∈ N.space ×ˢ J :=
        hfull ⟨hz.1, htime b hz.2⟩
      have hpair : w = (z.1, time b z.2) := hci hwJ hzJ heq
      have ht := congrArg Prod.snd hpair
      dsimp only at ht
      cases b <;> dsimp [time] at ht hwt <;> nlinarith
    · intro hzero
      refine ⟨(z.1, if b then ε else -ε), ⟨hz.1, rfl⟩, ?_⟩
      rw [hdvalue, hzero]
      cases b <;> simp [time]
  refine ⟨hdPL, hdembedding, hdQ, hdbase, hdzero, ?_⟩
  intro η hη hηone
  let u := ε + (δ - ε) * η
  have huε : ε < u := by dsimp [u]; nlinarith
  have huδ : u < δ := by dsimp [u]; nlinarith
  let a := if b then -ε else -u
  let v := if b then u else ε
  have hav : Ioo a v ⊆ Ioo (-δ) δ := by
    intro r hr
    cases b <;> dsimp [a, v] at hr <;> constructor <;> linarith [hr.1, hr.2]
  have hV := isOpen_collar_subinterval hc hδ hopen hav
  have heq : (Subtype.val : Q → X) ⁻¹' (d b '' (N.space ×ˢ Ico 0 η)) =
      (Subtype.val : Q → X) ⁻¹' (c '' (N.space ×ˢ Ioo a v)) := by
    ext x
    constructor
    · rintro ⟨z, hz, heq⟩
      refine ⟨(z.1, time b z.2), ⟨hz.1, ?_⟩, (hdvalue z).symm.trans heq⟩
      have hlo : ε ≤ ε + (δ - ε) * z.2 := by nlinarith [hz.2.1]
      have hhi : ε + (δ - ε) * z.2 < u := by dsimp [u]; nlinarith [hz.2.2]
      cases b <;> dsimp [time, a, v] <;> constructor <;> linarith
    · rintro ⟨z, hz, heq⟩
      have hnot : ¬(-ε < z.2 ∧ z.2 < ε) := by
        intro ht
        exact x.property.2 ⟨z, ⟨hz.1, ht⟩, heq⟩
      let r := ((if b then z.2 else -z.2) - ε) / (δ - ε)
      have hr : r ∈ Ico 0 η := by
        have hlo : ε ≤ if b then z.2 else -z.2 := by
          cases b
          · dsimp [a, v] at hz ⊢
            by_contra h
            exact hnot ⟨by linarith, hz.2.2⟩
          · dsimp [a, v] at hz ⊢
            by_contra h
            exact hnot ⟨hz.2.1, by linarith⟩
        have hhi : (if b then z.2 else -z.2) < u := by
          cases b <;> dsimp [a, v] at hz ⊢ <;> linarith [hz.2.1, hz.2.2]
        refine ⟨div_nonneg (sub_nonneg.mpr hlo) hwidth.le, ?_⟩
        apply (div_lt_iff₀ hwidth).mpr
        dsimp [u] at hhi
        linarith
      have htr : time b r = z.2 := by
        have hwne : δ - ε ≠ 0 := ne_of_gt hwidth
        cases b <;> dsimp [time, r] <;> field_simp <;> ring
      refine ⟨(z.1, r), ⟨hz.1, hr⟩, ?_⟩
      rw [hdvalue, htr]
      exact heq
  rw [heq]
  exact hV.preimage continuous_subtype_val

end PoincareConjecture.M76
