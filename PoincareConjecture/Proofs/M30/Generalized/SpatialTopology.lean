import PoincareConjecture.Proofs.M30.Generalized.BoxCylinder
import Mathlib.Topology.Separation.Hausdorff












set_option autoImplicit false

open Set Filter
open scoped Topology

universe u v

namespace PoincareConjecture.M30.Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {M : Type v}
  {p : M → C.carrier}



theorem continuous_family_pointMap [TopologicalSpace M]
    (e : ∀ a : M, GeneralizedFlowCylinder F C origin scale I {p a})
    (hI : I.OrdConnected)
    (hf : ∀ t (ht : t ∈ I), Continuous (fun a => (e a).forward t ht (p a))) :
    Continuous (fun z : I × M => (e z.2).pointMap z.1.1 z.1.2 (p z.2)) := by
  classical
  rw [continuous_iff_continuousAt]
  rintro ⟨s, a⟩
  obtain ⟨b, y, delta, hdelta, hb⟩ :=
    (e a).vertical_compatibility s.1 s.2 (p a) (mem_singleton (p a))
  obtain ⟨hbs, hse⟩ := hb s.1 s.2 (by simpa using hdelta)
  have htime : ∀ᶠ t : I in 𝓝 s, origin + t.1 / scale ∈ (F.box b).interval := by
    have hnear : {t : I | |t.1 - s.1| < delta} ∈ 𝓝 s := by
      apply (isOpen_lt (continuous_subtype_val.sub continuous_const).abs
        continuous_const).mem_nhds
      simpa using hdelta
    filter_upwards [hnear] with t ht
    exact (hb t.1 t.2 ht).choose
  let clock : I → (F.box b).interval := fun t =>
    if ht : origin + t.1 / scale ∈ (F.box b).interval then
      ⟨origin + t.1 / scale, ht⟩ else ⟨origin + s.1 / scale, hbs⟩
  have hclock_eq : (fun t : I => (clock t).1) =ᶠ[𝓝 s]
      (fun t => origin + t.1 / scale) := by
    filter_upwards [htime] with t ht
    simp only [clock, dif_pos ht]
  have hclock : ContinuousAt clock s := by
    apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    have hreal : ContinuousAt (fun t : I => origin + t.1 / scale) s :=
      (continuous_const.add (continuous_subtype_val.div_const scale)).continuousAt
    exact hreal.congr_of_eventuallyEq hclock_eq
  let fs := fun z : M => (e z).forward s.1 s.2 (p z)
  let spatial := (F.box b).inverse (origin + s.1 / scale) hbs ∘ fs
  have ha : fs a ∈ range ((F.box b).forward _ hbs) := ⟨y, hse.symm⟩
  have hnear : ∀ᶠ z in 𝓝 a, fs z ∈ range ((F.box b).forward _ hbs) :=
    (hf s.1 s.2).continuousAt.preimage_mem_nhds
      (((F.box b).forward_openEmbedding _ hbs).isOpen_range.mem_nhds ha)
  have hspatial : ContinuousAt spatial a :=
    (((F.box b).inverse_smooth _ hbs).continuousOn.continuousAt
      (((F.box b).forward_openEmbedding _ hbs).isOpen_range.mem_nhds ha)).comp
        (hf s.1 s.2).continuousAt
  let B := fun z : I × M =>
    (⟨(clock z.1).1, (F.box b).forward _ (clock z.1).2 (spatial z.2)⟩ : F.point)
  have hpair : ContinuousAt (fun z : I × M => (clock z.1, spatial z.2)) (s, a) :=
    (ContinuousAt.comp (x := (s, a)) (g := clock) (f := Prod.fst)
      hclock continuous_fst.continuousAt).prodMk
      (ContinuousAt.comp (x := (s, a)) (g := spatial) (f := Prod.snd)
        hspatial continuous_snd.continuousAt)
  have hB : ContinuousAt B (s, a) :=
    (F.box_openEmbedding b).continuous.continuousAt.comp hpair
  apply hB.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt htime,
    continuous_snd.continuousAt hnear] with z hzt hzs
  have heq := forward_eq_box_on_overlap (e z.2) hI (mem_singleton (p z.2)) b
    (spatial z.2) s.2 hbs (((F.box b).right_inverse _ hbs hzs).symm)
      z.1.1 z.1.2 hzt
  have hclock_at : clock z.1 = ⟨origin + z.1.1 / scale, hzt⟩ := dif_pos hzt
  dsimp only [B]
  rw [hclock_at]
  exact congrArg (fun w => (⟨origin + z.1.1 / scale, w⟩ : F.point)) heq



theorem injective_family_pointMap
    (e : ∀ a : M, GeneralizedFlowCylinder F C origin scale I {p a})
    (hI : I.OrdConnected) {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    (hinitial : Function.Injective (fun a => (e a).forward s₀ hs₀ (p a))) :
    Function.Injective (fun z : I × M => (e z.2).pointMap z.1.1 z.1.2 (p z.2)) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ heq
  have hst : s = t := Subtype.ext
    ((parabolicTimeInv_strictMono scale (e a).scale_pos origin).injective
      (congrArg Sigma.fst heq))
  subst t
  have hzero := pointMap_eq_on_interval (e a) (e b) hI
    (mem_singleton (p a)) (mem_singleton (p b)) s.2 heq s₀ hs₀
  have hab := hinitial (eq_of_heq (Sigma.mk.inj_iff.mp hzero).2)
  exact Prod.ext rfl hab




theorem isEmbedding_family_pointMap_on_compact [TopologicalSpace M]
    (e : ∀ a : M, GeneralizedFlowCylinder F C origin scale I {p a})
    (hI : I.OrdConnected) (hIc : IsCompact I)
    (hf : ∀ t (ht : t ∈ I), Continuous (fun a => (e a).forward t ht (p a)))
    {s₀ : ℝ} (hs₀ : s₀ ∈ I)
    (hinitial : Function.Injective (fun a => (e a).forward s₀ hs₀ (p a)))
    {K : Set M} (hK : IsCompact K) :
    Topology.IsEmbedding
      (fun z : I × K => (e z.2.1).pointMap z.1.1 z.1.2 (p z.2.1)) := by
  let : CompactSpace I := isCompact_iff_compactSpace.mp hIc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : T2Space F.point := F.space_t2
  have hc : Continuous
      (fun z : I × K => (e z.2.1).pointMap z.1.1 z.1.2 (p z.2.1)) :=
    (continuous_family_pointMap e hI hf).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply (hc.isClosedEmbedding ?_).isEmbedding
  exact (injective_family_pointMap e hI hs₀ hinitial).comp
    (Function.Injective.prodMap Function.injective_id Subtype.val_injective)

end PoincareConjecture.M30.Cylinder
