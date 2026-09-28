import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies
import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.PathHomotopy

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.AnnulusSquareCopies

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)
local notation "O" => (Set.ofPred (fun x : P2 ↦ x ∈ squareAnnulus 8 1 ∧ depth 8 x = -1))

theorem exists_nonnull_outer_rim_of_paths
    {X : Type*} [TopologicalSpace X] {R : Set X}
    {f : Fin 2 → P2 → X} {g : P2 → X} (C : AnnulusSquareCopies f g)
    (hg : ContinuousOn g (squareAnnulus 8 1)) (hgR : MapsTo g (squareAnnulus 8 1) R)
    {x y : R} (A B : Path x y)
    (hA : ∀ t : I, (A t : X) = f 0 (t, 0))
    (hB : ∀ t : I, (B t : X) = f 1 (t, 0))
    (hnon : ¬ (A.trans B.symm).Homotopic (Path.refl x)) :
    ∃ rim : C(O, R), (∀ z : O, (rim z : X) = g z) ∧ ¬ rim.Nullhomotopic := by
  let rim : C(O, R) :=
    { toFun z := ⟨g z, hgR z.property.1⟩
      continuous_toFun := (hg.comp_continuous continuous_subtype_val
        (fun z ↦ z.property.1)).subtype_mk _ }
  let z (t : I) : Sq := ⟨(t, 0), t.property, by norm_num⟩
  let w (j : Fin 2) (t : I) : O :=
    ⟨C.chart j (z t), C.chart_mem j (z t), (C.outer j (z t)).mpr rfl⟩
  have hw (j : Fin 2) : Continuous (w j) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp ((C.chart j).continuous.comp (by fun_prop))
  have hzero : w 0 0 = w 1 0 :=
    Subtype.ext ((C.cross (z 0) (z 0)).mpr ⟨rfl, Or.inl rfl⟩)
  have hone : w 0 1 = w 1 1 :=
    Subtype.ext ((C.cross (z 1) (z 1)).mpr ⟨rfl, Or.inr rfl⟩)
  let P : Path (w 0 0) (w 0 1) := ⟨⟨w 0, hw 0⟩, rfl, rfl⟩
  let Q : Path (w 0 0) (w 0 1) := ⟨⟨w 1, hw 1⟩, hzero.symm, hone.symm⟩
  let L := P.trans Q.symm
  have hvalues (t : I) : ((L.map rim.continuous) t : X) = (A.trans B.symm) t := by
    change g (L t) = ((A.trans B.symm) t : X)
    simp only [L, Path.trans_apply, Path.symm_apply]
    split_ifs
    · exact (C.val 0 _).trans (hA _).symm
    · exact (C.val 1 _).trans (hB _).symm
  have hbase : rim (w 0 0) = x := by
    apply Subtype.ext
    exact (C.val 0 (z 0)).trans ((hA 0).symm.trans (congrArg Subtype.val A.source))
  refine ⟨rim, fun _ ↦ rfl, ?_⟩
  intro hnull
  have h := Path.Homotopic.map_nullhomotopic_of_nullhomotopic hnull L
  have hleft : (L.map rim.continuous).toContinuousMap = (A.trans B.symm).toContinuousMap :=
    ContinuousMap.ext (fun t ↦ Subtype.ext (hvalues t))
  have hright : (Path.refl (rim (w 0 0))).toContinuousMap = (Path.refl x).toContinuousMap :=
    ContinuousMap.ext (fun _ ↦ hbase)
  change (L.map rim.continuous).toContinuousMap.HomotopicRel
    (Path.refl (rim (w 0 0))).toContinuousMap {0, 1} at h
  rw [hleft, hright] at h
  exact hnon h

end PoincareConjecture.M76.Dehn.AnnulusSquareCopies
