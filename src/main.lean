import tactic

noncomputable theory

namespace test 

notation `Set` := Type 0
def relation := Set → Set → Prop
constant mem  : relation

instance : has_mem Set Set :=
⟨mem⟩


def fclass := Set → Prop
def is_set (X : fclass) : Prop := ∃(y : Set), ∀(z : Set), z ∈ y ↔ X z 
def proper_class (X : fclass) : Prop := ¬is_set X

def set_of {φ : fclass} (h : is_set φ) : Set := classical.some h
@[simp]lemma mem_set_of (x : Set) {φ : fclass} (h : is_set φ) : x ∈ set_of h ↔ φ x := 
(classical.some_spec h) x

def mem_class (a : Set) (X : fclass) := X a

instance : has_mem Set fclass := ⟨mem_class⟩

lemma existence : nonempty Set := nonempty_of_inhabited


@[ext] axiom extensionality_axiom : ∀(x y : Set), (∀(z : Set), z ∈ x ↔ z ∈ y) → x = y
axiom specification_axiom : 
∀(x : Set) (φ : fclass), ∃(y : Set), ∀(z : Set), z ∈ y ↔ (z ∈ x ∧ φ z)
axiom pairing_axiom : ∀(x y : Set), ∃(z : Set), x ∈ z ∧ y ∈ z
axiom union_axiom : ∀(F : Set), ∃(A : Set), ∀(Y x : Set), Y ∈ F → x ∈ Y → x ∈ A

lemma existence' : ∃(x : Set), true := 
begin 
	cases existence,
	use val,
end

def is_empty (x : Set) : Prop := ∀z, z ∉ x
theorem empty_set_exists : ∃x, is_empty x := 
begin 
	cases existence with x,
	let φ := λz, z ≠ z,
	cases specification_axiom x φ with y hy,
	use y,
	intros z hz,
	specialize hy z,
	rw hy at hz,
	exact not_imp.mpr hz (congr_fun rfl),
end

def empty_set := classical.some empty_set_exists

instance : has_emptyc Set := ⟨empty_set⟩ 

theorem empty_set_is_empty : is_empty ∅ := classical.some_spec empty_set_exists

def empty_set_unique : ∀x, is_empty x ↔ x = ∅ :=
begin 
	intro x,
	split,
	{
		intro h,
		ext,
		split,
		intro hx,
		specialize h z,
		contradiction,


		intro hempty,
		have temp := empty_set_is_empty z,
		contradiction,
	},
	{
		intro h,
		rw h,
		exact empty_set_is_empty,
	},
end

def subset (x y : Set) : Prop := ∀ ⦃z⦄, z ∈ x → z ∈ y
instance : has_subset Set := ⟨subset⟩

lemma subset_iff (x y : Set) : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y := by refl

def subset_class (x : Set) (φ : fclass) : Prop := ∀⦃z : Set⦄, z ∈ x → φ z

def transitive (z : Set) : Prop := ∀⦃x⦄, x ∈ z → x ⊆ z
def transitive_class (φ : fclass) := ∀⦃x y: Set⦄, φ x → y ∈ x → φ y

def transitive_rel (z : Set) (R : relation) : Prop := ∀{a b c : Set}, a ∈ z → b ∈ z → c ∈ z →
 R a b → R b c → R a c 
 def transitive_rel_class (φ : fclass) (R : relation) : Prop := ∀{a b c : Set}, φ a → φ b → φ c →
 R a b → R b c → R a c 

def irreflexive (z : Set) (R : relation) : Prop := ∀{x : Set}, x ∈ z → ¬ R x x
def trichotomic (z : Set) (R : relation) : Prop := ∀{a b : Set}, a ∈ z → b ∈ z → R a b ∨ R b a ∨ a = b 
def minimal {z : Set} (R : relation) {x : Set} (hx : x ∈ z) : Prop := ∀⦃y : Set⦄, y ∈ z → ¬ R y x
def well_founded (z : Set) (R : relation) : Prop :=
 ∀{x}, x ⊆ z → x ≠ ∅ → ∃(y : Set) (hy : y ∈ x), minimal R hy

def irreflexive_class (φ : fclass) (R : relation) : Prop := ∀{x : Set}, φ x → ¬ R x x
def trichotomic_class (φ : fclass) (R : relation) : Prop := ∀{a b : Set}, φ a → φ b → R a b ∨ R b a ∨ a = b 
def minimal_class {φ : fclass} (R : relation) {x : Set} (hx : φ x) : Prop := ∀⦃y : Set⦄, φ y → ¬ R y x
def well_founded_class (φ : fclass) (R : relation) : Prop :=
 ∀{x}, subset_class x φ → x ≠ ∅ → ∃(y : Set) (hy : y ∈ x), minimal R hy

structure well_order (set : Set) (R : relation) :=
(irrfl : irreflexive set R)
(tran : transitive_rel set R)
(tri : trichotomic set R)
(wf : well_founded set R)

def is_well_order (x : Set) (R : relation) : Prop := nonempty (well_order x R)

structure well_order_class (φ : fclass) (R : relation) :=
(irrfl : irreflexive_class φ R)
(tran : transitive_rel_class φ R)
(tri : trichotomic_class φ R)
(wf : well_founded_class φ R)

structure ordinal (z : Set) :=
(tran : transitive z)
(wo : well_order z (∈))

structure ordinal_class (φ : fclass) :=
(tran : transitive_class φ)
(wo : well_order_class φ (∈))

lemma wo_set_of_wo_class {φ : fclass} {R : relation} (hwo : well_order_class φ R) (hset : is_set φ)
: well_order (set_of hset) R :=
{
	irrfl := begin
		intros x hx,
		rw mem_set_of at hx,
		exact hwo.irrfl hx,
	end,
	tran := begin 
		intros a b c ha hb hc hab hbc,
		rw mem_set_of at *,
		exact hwo.tran ha hb hc hab hbc,
	end,
	tri := begin 
		intros a b ha hb,
		rw mem_set_of at *,
		exact hwo.tri ha hb,
	end,
	wf := begin 
		intros X hX1 hX2,
		have : subset_class X φ,
		{
			unfold subset_class,
			rw subset_iff at hX1,
			simp at hX1,
			exact hX1,	
		},
		exact hwo.wf this hX2,
	end,
}

lemma ordinal_set_of_ordinal_class {φ : fclass} (hord : ordinal_class φ) (hset : is_set φ) :
ordinal (set_of hset) := 
{
	tran := begin 
		intros x hx y hyx,
		simp at *,
		exact hord.tran hx hyx,
	end,
	wo := wo_set_of_wo_class hord.wo hset
}


@[simp]lemma mem_empty (x : Set) : x ∈ (∅ : Set) ↔ false := iff_false_intro (empty_set_is_empty x)
lemma not_mem_empty {x : Set} (h : x ∈ (∅:Set)) : false := (mem_empty x).mp h

lemma empty_subset : ∀(x : Set), ∅ ⊆ x := 
begin 
	intros x y hy,
	exfalso,
	rw ← mem_empty y,
	exact hy,
end

lemma subset_self (x : Set) : x ⊆ x := λz hz, hz
lemma subset_trans : ∀ {x y z : Set}, x ⊆ y → y ⊆ z → x ⊆ z :=
begin 
	intros x y z hxy hyz w hw,
	exact hyz (hxy hw),
end

theorem eq_iff_subsets (x y : Set) : x = y ↔ x ⊆ y ∧ y ⊆ x := 
begin 
	split,
	{
		intro h,
		split; 
		rw h, 
		exact subset_self y,
		exact subset_self y,
	},
	intro h,
	ext,
	split,
	{
		intro hz,
		exact h.1 hz,
	},
	{
		intro hz,
		exact h.2 hz,
	},
end

lemma subset_empty_iff (x : Set) : x ⊆ ∅ ↔ x = ∅ :=
begin 
	split,
	{
		intro h,
		rw eq_iff_subsets,
		split, exact h,
		exact empty_subset x,
	},
	{
		intro h,
		rw h,
		exact subset_self ∅,
	},
end


lemma empty_is_ordinal : ordinal ∅ := {
	tran := begin 
			intros x hx,
			exfalso,
			rw ← mem_empty x,
			exact hx,
	end,
	wo := {
		irrfl := begin 
				intros x hx,
				exfalso,
				rw ← mem_empty x,
				exact hx,
		end,
		tran := begin 
				intros a b c ha,
				exfalso,
				rw ← mem_empty a,
				exact ha,
		end,
		tri := begin 
				intros a b ha,
				exfalso,
				rw ← mem_empty a,
				exact ha,
		end,
		wf := begin 
			intros a ha ha_nonempty,
			exfalso,
			rw subset_empty_iff a at ha,
			exact ha_nonempty ha,
		end,
	},
}

def ON : fclass := λx, nonempty (ordinal x)
theorem empty_set_is_ordinal : ∅ ∈ ON := nonempty.intro empty_is_ordinal

def univ : fclass := λx, true 
theorem univ_is_proper_class : proper_class univ := 
begin 
	intro h,
	cases h with V hV,
	cases specification_axiom V (λx, x ∉ x) with R hR,
	specialize hR R,
	rw hV R at hR,
	unfold univ at hR,
	simp at hR,
	exact hR,
end

instance : has_sep Set Set :=
⟨λp s, classical.some (specification_axiom s p)⟩

@[simp]lemma mem_sep (s : Set) (f : fclass) : ∀x, x ∈ {a ∈ s | f a} ↔ x ∈ s ∧ f x :=
classical.some_spec (specification_axiom s f)

def subclass_set (φ : fclass) (x : Set) := ∀⦃y⦄, φ y → y ∈ x

theorem subclass_of_set_is_set {φ : fclass} {x : Set} (h : subclass_set φ x) :
 is_set φ := 
begin 
	cases specification_axiom x φ with y hy,
	use y,
	intros z,
	specialize hy z,
	rw hy,
	split,
	{
		intro h1,
		exact h1.2,
	},
	{
		intro h1,
		split,
		exact h h1,
		exact h1,
	},
end

lemma pair_set_exists (x y : Set) : ∃(z : Set), ∀w, w ∈ z ↔ w = x ∨ w = y := 
begin 
	cases pairing_axiom x y with k hk,
	have h : subclass_set (λn, n = x ∨ n = y) k,
	{
		intros n hn,
		cases hn,
		rw hn,
		exact hk.1,

		rw hn,
		exact hk.2
	},

	cases subclass_of_set_is_set h with P hP,
	use P,
	simp at hP,
	exact hP,
end

def pair_set (x y : Set) : Set := classical.some (pair_set_exists x y)

lemma pair_set_is_pair (x y : Set) : ∀w, w ∈ (pair_set x y) ↔ w = x ∨ w = y := 
classical.some_spec (pair_set_exists x y)

@[simp]lemma mem_pair (z x y: Set) : z ∈ pair_set x y ↔ z = x ∨ z = y := pair_set_is_pair x y z

def sing (x : Set) := pair_set x x
@[simp]lemma mem_sing (y x : Set) : y ∈ sing x ↔ y = x := 
begin
	unfold sing,
	rw mem_pair,
	exact or_self (y = x),
end

lemma sing_is_sing (x : Set) : ∀y, y ∈ sing x ↔ y = x := λy : Set, mem_sing y x

lemma sing_unique (x y : Set) : (∀z, z ∈ y ↔ z = x) → y = sing x := 
begin 
	intro h,
	ext,
	rw mem_sing,
	exact h z,
end

theorem union_exists (F : Set) : ∃(A : Set), ∀x, x ∈ A ↔ ∃Y ∈ F, x ∈ Y :=
begin
	cases union_axiom F with B hB,
	have h : subclass_set (λx, ∃Y ∈ F, x ∈ Y) B,
	{
		intros x hx,
		cases hx with Y hY,
		cases hY with hY hxY,
		exact hB Y x hY hxY,
	},
	cases subclass_of_set_is_set h with A hA,
	use A,
	simp at hA,
	intros x,
	rw hA x,
	exact bex_def.symm,
end


def union (F : Set) := classical.some (union_exists F)
lemma union_is_union (F : Set) : ∀x, x ∈ union F ↔ ∃Y ∈ F, x ∈ Y :=
classical.some_spec (union_exists F)

@[simp] lemma mem_union (x F : Set) : x ∈ union F ↔ ∃Y ∈ F, x ∈ Y := union_is_union F x

def pair_union (a b : Set) : Set :=
union (pair_set a b)

instance : has_union Set :=
⟨pair_union⟩

@[simp]lemma mem_pair_union (x a b : Set) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
begin 
	unfold has_union.union,
	unfold pair_union,
	rw mem_union,
	split,
	{
		intro h,
		rcases h with ⟨Y, hY, hxY⟩,
		rw mem_pair at hY,
		cases hY,
		{
			left,
			rw ← hY,
			exact hxY
		},
		{
			right,
			rw ← hY,
			exact hxY,
		},
	},
	{
		intros h,
		cases h,
		{
			use a,
			rw mem_pair,
			simp,
			exact h,
		},
		{
			use b,
			rw mem_pair,
			simp,
			exact h,
		},
	},
end

def pair_inter (a b : Set) : Set := classical.some (specification_axiom (a ∪ b) (λz, z ∈ a ∧ z ∈ b))
instance : has_inter Set :=
⟨pair_inter⟩

@[simp]lemma mem_pair_inter (x a b : Set) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := 
begin 
	unfold has_inter.inter,
	unfold pair_inter,
	have := classical.some_spec (specification_axiom (a ∪ b) (λz, z ∈ a ∧ z ∈ b)),
	specialize this x,
	finish,
end

lemma pair_inter_subset_left (a b : Set) : (a ∩ b) ⊆ a := 
begin 
	intros x hx,
	rw mem_pair_inter at hx,
	exact hx.1,
end

lemma pair_inter_subset_right (a b : Set) : (a ∩ b) ⊆ b := 
begin 
	intros x hx,
	rw mem_pair_inter at hx,
	exact hx.2,
end

lemma pair_inter_symm (a b : Set) : a ∩ b = b ∩ a := 
begin 
	ext,
	split,
	repeat {
		intro z,
		simp at *,
		exact and.comm.mp z,
	},
end

lemma eq_pair_inter_left_iff (a b : Set) : a ∩ b = a ↔ a ⊆ b :=
begin 
	split,
	{
		intro h,
		rw ← h,
		exact pair_inter_subset_right a b, 
	},
	{
		intro h,
		ext,
		split,
		{
			intro hz,
			rw mem_pair_inter at hz,
			exact hz.1,
		},
		{
			intro hz,
			rw mem_pair_inter,
			exact ⟨hz, h hz⟩,
		},
	}
end

lemma eq_pair_inter_right_iff (a b : Set) : a ∩ b = b ↔ b ⊆ a :=
begin 
	rw pair_inter_symm a b,
	exact eq_pair_inter_left_iff b a,
end

def succ (x : Set) : Set := x ∪ sing x
@[simp]lemma mem_succ (y x : Set) : y ∈ succ x ↔ y ∈ x ∨ y = x := 
begin
	unfold succ,
	simp,
end

instance : has_lt Set := ⟨λ s t, s ∈ t⟩
instance : has_le Set := ⟨λ s t, s ∈ t ∨ s = t⟩

@[simp]lemma le_iff (a b : Set) : a ≤ b ↔ a ∈ b ∨ a = b := by refl

lemma lt_succ_self (x : Set) : x < succ x := 
begin 
	unfold has_lt.lt,
	simp,
end

lemma subset_of_wo_is_wo {x y : Set} {R : relation} (hxy : x ⊆ y) (hy : well_order y R) : 
is_well_order x R := 
begin
	have hx : well_order x R := {
		irrfl := λz hz, hy.irrfl (hxy hz),
		tran := λa b c ha hb hc hab hbc, hy.tran (hxy ha) (hxy hb) (hxy hc) hab hbc,
		tri := λ a b hax hbx,hy.tri (hxy hax) (hxy hbx),
		wf := λz hzx hz_nonempty, hy.wf (subset_trans hzx hxy) hz_nonempty,
	},

	exact nonempty.intro hx,
end

lemma ord_not_mem_self {x : Set} (hx : ON x) : x ∉ x := 
begin 
	by_contra h,
	unfold ON at hx,
	cases hx,
	exact hx.wo.irrfl h h,
end

lemma ON_is_transitive : transitive_class ON :=
begin 
	intros x y hx hyx,
	cases hx with x_ord,

	have y_sub_x : y ⊆ x := x_ord.tran hyx,
	cases subset_of_wo_is_wo y_sub_x x_ord.wo with y_wo,

	have hy_is_on : ordinal y := {
		tran := begin 
			intros a hay z hza,
			have hax := x_ord.tran hyx hay,
			have hzx := x_ord.tran hax hza,
			exact x_ord.wo.tran hzx hax hyx hza hay,
		end,
		wo := y_wo,
	},

	exact nonempty.intro hy_is_on,
end

lemma mem_of_ordinal_is_ordinal {x y: Set} (hx : x ∈ ON) (hyx : y ∈ x) : ON y :=
ON_is_transitive hx hyx

lemma diff_exists (x y : Set) : ∃(z : Set), ∀a, a ∈ z ↔ (a ∈ x ∧ a ∉ y) := specification_axiom x (λa, a ∉ y)

def diff (x y : Set) : Set := classical.some (diff_exists x y)

instance : has_sdiff Set :=
⟨diff⟩

@[simp]lemma mem_diff (z x y : Set) : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := classical.some_spec (diff_exists x y) z
lemma in_diff {z x y : Set} : z ∈ x → z ∉ y → z ∈ x \ y := 
begin 
	intros h1 h2,
	simp,
	exact ⟨h1, h2⟩,
end

lemma nonempty_has_mem {x : Set} (h : x ≠ ∅) : ∃y, y ∈ x := 
begin 
	by_contra h2,
	push_neg at h2,
	have := empty_set_unique x,
	unfold is_empty at this,
	rw this at h2,
	exact h h2,
end

lemma diff_subset (x y : Set) : x \ y ⊆ x := begin 
	intros z hz,
	simp at hz,
	exact hz.1,
end

lemma pair_inter_ordinal {a b : Set} (ha : ordinal a) (hb : ordinal b) : ordinal (a ∩ b) :=
{
	tran := begin 
		intros x hx z hzx,
		simp at *,
		exact ⟨ha.tran hx.1 hzx, hb.tran hx.2 hzx⟩,
	end,
	wo := begin 
		have := subset_of_wo_is_wo (pair_inter_subset_left a b) ha.wo,
		unfold is_well_order at this,
		exact classical.some (classical.exists_true_of_nonempty this),
	end
}

lemma not_rel_min {X x y : Set} {R : relation} {hxX : x ∈ X} (hx_min : minimal R hxX) (hy : R y x)
 : y ∉ X := λh, hx_min h hy

lemma le_iff_subset {x y : Set} (x_ord : ON x) (y_ord : ON y) : x ⊆ y ↔ x ≤ y :=
begin 
	tactic.unfreeze_local_instances,
	cases x_ord,
	cases y_ord,
	split,
	{
		intro h,

		let X := y \ x,
		by_cases X_nonempty : X ≠ ∅,
		{
			left,
			rcases y_ord.wo.wf (diff_subset y x) X_nonempty with ⟨ξ, hξ_diff, hξ_min⟩,
			have hξy : ξ ∈ y := (diff_subset y x) hξ_diff,

			suffices hξ_is_x : ξ = x,{rw ← hξ_is_x, exact hξy},
			rw eq_iff_subsets, split,
			{
				intros μ hμ,
				by_contra hμ_not_in_x,
				apply not_rel_min hξ_min hμ,
				simp,
				exact ⟨y_ord.tran hξy hμ, hμ_not_in_x⟩,
			},
			{
				by_contra h_contra,
				rw subset_iff at h_contra,
				push_neg at h_contra,
				rcases h_contra with ⟨μ, hμx, hμ_notξ⟩,
				have hμy := h hμx,
				have h_or : μ = ξ ∨ ξ ∈ μ,
				{
					have := y_ord.wo.tri hξy hμy,
					tauto,
				},
				cases h_or,
				{
					rw mem_diff at hξ_diff,
					rw h_or at hμx,
					exact hξ_diff.2 hμx,
				},
				have := x_ord.tran hμx h_or,
				rw mem_diff at hξ_diff,
				exact hξ_diff.2 this,
			},
		},
		{
			simp at X_nonempty,
			right,
			rw eq_iff_subsets, split, exact h,
			intros z hzy,
			by_contra hzx,
			have contra := in_diff hzy hzx,
			have : z ∈ X := contra,
			rw X_nonempty at this,
			simp at this, exact this,
		},
	},
	{
		intro h,
		cases h,
		exact y_ord.tran h,

		rw h,
		exact subset_self y,
	},
end

theorem ON_ordinal_class : ordinal_class ON :=
{
	tran := ON_is_transitive,
	wo := 
	{
		irrfl := λx hx, ord_not_mem_self hx,
		tran := begin 
			intros a b c ha hb hc hab hbc,
			cases hc,
			exact hc.tran hbc hab,
		end,
		tri := begin
			intros a b ha hb,
			cases ha,
			cases hb,

			have hinter := pair_inter_ordinal ha hb,
			have hinter_a := pair_inter_subset_left a b,
			have hinter_b := pair_inter_subset_right a b,
			
			rw le_iff_subset (nonempty.intro hinter) (nonempty.intro ha) at hinter_a,
			rw le_iff_subset (nonempty.intro hinter) (nonempty.intro hb) at hinter_b,
			simp at *,
			by_cases a ∩ b = a ∨ a ∩ b = b,
			{
				rw eq_pair_inter_left_iff a b at h,
				rw eq_pair_inter_right_iff a b at h,
				cases h,
				{
					rw le_iff_subset (nonempty.intro ha) (nonempty.intro hb) at h,
					rw le_iff at h,
					finish,
				},
				{
					rw le_iff_subset (nonempty.intro hb) (nonempty.intro ha) at h,
					rw le_iff at h,
					finish,
				},
			},
			push_neg at h,
			have : a ∩ b ∈ a ∧ a ∩ b ∈ b := by finish,
			rw ← mem_pair_inter (a ∩ b) a b at this,
			exfalso,
			exact ord_not_mem_self (nonempty.intro hinter) this,
		end,
		wf := begin 
			intros X hX1 hX2,
			cases nonempty_has_mem hX2 with a ha,
			by_cases a ∩ X = ∅,
			{
				use a,
				use ha,
				intros x hxX hxa,
				have : x ∈ a ∩ X, {rw mem_pair_inter, exact ⟨hxa, hxX⟩,},
				rw h at this,
				exact (mem_empty x).mp this,
			},
			{
				have a_ord : ordinal a,
				{
					have := (hX1 ha),
					unfold ON at this,
					exact classical.some (classical.exists_true_of_nonempty this),
				},
				have h_wo := subset_of_wo_is_wo (pair_inter_subset_left a X) a_ord.wo,
				cases h_wo,
				rcases h_wo.wf (subset_self (a ∩ X)) h with ⟨ξ, hξaX, hξ_min⟩,
				use ξ,
				rw mem_pair_inter at hξaX,
				use hξaX.2,
				
				intros b hbX hbξ,
				have hba := a_ord.tran hξaX.1 hbξ,
				have hbaX : b ∈ a ∩ X, {rw mem_pair_inter at *, exact ⟨hba, hbX⟩},

				exact hξ_min hbaX hbξ,
			},
		end,
	}
}

theorem ON_is_proper_class : proper_class ON :=
begin 
	intro h,
	have h_ord := ordinal_set_of_ordinal_class ON_ordinal_class h,
	have : set_of h ∈ set_of h,
	{
		rw mem_set_of,
		exact nonempty.intro h_ord,
	},

	exact ord_not_mem_self (nonempty.intro h_ord) this,
end

theorem mem_ord_is_ord {x y : Set}  (y_ord : ordinal y) (h : x ∈ y) : ordinal x :=
classical.some (classical.exists_true_of_nonempty (ON_is_transitive (nonempty.intro y_ord) h))

theorem succ_of_ordinal_is_ordinal {z : Set} (h : ordinal z) : ordinal (succ z) := {
	tran := begin
		intros x hx y hy,
		
		simp at *,
		cases hx,
		{
			left,
			exact h.tran hx hy,
		},
		{
			left,
			rw ← hx,
			exact hy,
		},
	end,
	wo := {
		irrfl := begin 
			intros x hxSz hxx,
			rw mem_succ at hxSz,
			cases hxSz,
			{exact (mem_ord_is_ord h hxSz).wo.irrfl hxx hxx},
			{
				rw hxSz at hxx,
				exact ord_not_mem_self (nonempty.intro h) hxx,
			}
		end,
		tran := begin 
			intros a b c ha hb hc hab hbc,
			rw mem_succ at *,
			cases hc,
			{
				have c_ord := mem_ord_is_ord h hc,
				have hbz := h.tran hc hbc,
				exact c_ord.tran hbc hab,
			},
			{
				rw hc at *,
				exact h.tran hbc hab,
			},
		end,
		tri := begin 
			intros a b ha hb,
			rw mem_succ at *,
			cases hb,
			{
				cases ha,
				{exact h.wo.tri ha hb},
				{rw ha, right,left, exact hb},
			},
			{
				rw hb,
				finish,
			},
		end,
		wf := begin 
			intros X hX1 hX2,
			by_cases h_empty : X \ sing z = ∅,
			{
				use z,
				have hX_singz: X = sing z,
				{
					ext k,
					split,
					{
						intro hk,
						rw mem_sing,
						by_contra hh,
						have hknz : k ∉ sing z, {intro hkz, rw mem_sing at hkz, exact hh hkz},
						have : k ∈ (X \ sing z), {rw mem_diff, exact ⟨hk, hknz⟩},
						rw h_empty at this,
						exact (mem_empty k).mp this,
					},
					{
						intro hk, rw mem_sing at hk,
						have : ∀t, t ∈ X → t = z,
						{
							intros t ht,
							by_contra htz,
							have : t ∉ sing z, {intro temp, rw mem_sing at temp, exact htz temp},
							have contra : t ∈ X \ sing z, {rw mem_diff, exact ⟨ht, this⟩},
							rw h_empty at contra,
							exact (mem_empty t).mp contra,
						},
						cases nonempty_has_mem hX2 with α hα,
						specialize this α hα,
						rw hk,
						rw ← this,
						exact hα,
					},
				},
				have hz : z ∈ X, {rw hX_singz, simp,},
				use hz,
				intros a haX haz,
				rw hX_singz at *, simp at *,
				rw haX at haz,
				exact ord_not_mem_self (nonempty.intro h) haz,
			},
			{
				have hX_ss : X \ sing z ⊆ z,
				{
					intros t ht,
					simp at ht,
					specialize hX1 ht.1,
					rw mem_succ at hX1,
					tauto,
				},

				rcases h.wo.wf hX_ss h_empty with ⟨ξ, hξ_in, hξ_min⟩,
				use ξ,
				rw mem_diff at hξ_in,
				use hξ_in.1,

				intros t htX hcontra,
				specialize hX1 hξ_in.1, rw mem_succ at hX1,
				have ht : t ∈ X \ sing z,
				{
					rw mem_diff, use htX,
					intro temp, rw mem_sing at temp,
					cases hX1,

					rw temp at hcontra,
					exact ord_not_mem_self (nonempty.intro h) (h.tran hX1 hcontra),

					rw temp at hcontra,
					rw hX1 at hcontra,
					exact ord_not_mem_self (nonempty.intro h) hcontra,
				},
				exact hξ_min ht hcontra,
			},
		end,
	}
}

lemma not_ord_mem_ord {x y : Set} (x_ord : ordinal x) : x ∈ y → y ∈ x → false :=
λhxy hyx, ord_not_mem_self (nonempty.intro x_ord) (x_ord.tran hyx hxy)

lemma succ_inj_on_ON {x y : Set} (x_ord : ordinal x) (h : succ x = succ y) : x = y :=
begin 
	have hx := lt_succ_self x,
	have hy := lt_succ_self y,
	unfold has_lt.lt at *,
	rw h at hx,
	rw ← h at hy,
	rw mem_succ at *,
	by_cases hx_eq_y : x = y, exact hx_eq_y,
	exfalso,

	have hxy : x ∈ y := by tauto!,
	exact not_ord_mem_ord x_ord hxy (by tauto!),
end

def is_successor {x : Set} (x_ord : ordinal x) : Prop := ∃{y : Set} (hy : ordinal y), x = succ y
def is_limit {x : Set} (x_ord : ordinal x) : Prop := x ≠ ∅ ∧ ¬is_successor x_ord

def nat : fclass := λx, x ∈ ON ∧ ∀⦃y : Set⦄ (y_ord : ordinal y), y ≤ x → y = ∅ ∨ is_successor y_ord

lemma empty_is_nat : ∅ ∈ nat := 
begin 
	split, exact empty_set_is_ordinal,
	intros y y_ord h,
	rw le_iff at h,
	cases h,
	{
		exfalso,
		exact not_mem_empty h,
	},
	{exact or.inl h},
end

lemma le_self (x : Set) : x ≤ x := or.inr rfl

lemma le_tran {x y z : Set} (x_ord : ordinal x) (y_ord : ordinal y) (z_ord : ordinal z)
 (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z :=
begin
	cases hyz,
	{
		cases hxy,
		{
			left,
			exact z_ord.tran hyz hxy,
		},
		{
			left,
			rw hxy,
			exact hyz,
		},
	},
	{
		rw ← hyz,
		exact hxy,
	},
end

lemma ord_of_mem_ON {x : Set} (h : x ∈ ON) : ordinal x :=
classical.some (classical.exists_true_of_nonempty h)

lemma mem_ON_of_ord {x : Set} (x_ord : ordinal x) : x ∈ ON := nonempty.intro x_ord

lemma nat_is_ord {x : Set} (x_nat : x ∈ nat) : ordinal x := ord_of_mem_ON x_nat.1

lemma mem_of_nat_is_nat {x y : Set} (x_nat : x ∈ nat) (hyx : y ∈ x) : y ∈ nat :=
begin 
	have x_ord := nat_is_ord x_nat,
	have hy_ord := mem_of_ordinal_is_ordinal (nonempty.intro x_ord) hyx,
	have y_ord := ord_of_mem_ON hy_ord,

	split, 
	{exact hy_ord},
	{
		intros z z_ord hz_le_y,
		have hy_le_x : y ≤ x := or.inl hyx,
		have z_le_x : z ≤ x := le_tran z_ord y_ord x_ord hz_le_y hy_le_x,
		cases x_nat with __ hx,
		exact hx z_ord z_le_x
	}
end

lemma succ_of_nat_is_nat {x : Set} (x_nat : x ∈ nat) : succ x ∈ nat :=
begin
	have x_ord := (ord_of_mem_ON x_nat.1),
	split,
	{exact nonempty.intro (succ_of_ordinal_is_ordinal x_ord)},
	{
		intros y y_ord hyx,
		cases hyx,
		{
			rw mem_succ at hyx,
			cases hyx,
			{
				exact (mem_of_nat_is_nat x_nat hyx).2 y_ord (le_self y),
			},
			{
				cases x_nat.2 x_ord (le_self x),
				left, exact (rfl.congr h).mp hyx,
				right,
				rcases h with ⟨a, a_ord, ha⟩,
				use a,
				use a_ord,
				exact (rfl.congr ha).mp hyx, 
			},
		},
		{
			right,
			use x,
			use ord_of_mem_ON x_nat.1,
			exact hyx,
		},
	}
end

def is_inductive (x : Set) : Prop := ∅ ∈ x ∧ ∀⦃y⦄, y ∈ x → succ y ∈ x
def inductive_class (φ : fclass) : Prop := ∅ ∈ φ ∧ ∀⦃y⦄, y ∈ φ → succ y ∈ φ

lemma non_zero_nat_is_succ {x : Set} (x_nat : x ∈ nat) : x ≠ ∅ → 
is_successor (ord_of_mem_ON x_nat.1) :=
begin 
	intro h,
	cases x_nat with x_ord hx,
	specialize hx (ord_of_mem_ON x_ord) (le_self x),
	have : is_successor (ord_of_mem_ON x_ord) := by tauto!,
	rcases this with ⟨a, a_ord, ha⟩,
	use a,
	use a_ord,
	exact ha,
end

theorem inductive_class_contains_nat {I : fclass} (hI : inductive_class I) : ∀⦃x⦄, x ∈ nat → x ∈ I :=
begin 
	intros x x_nat,
	by_contra h,
	have temp : is_set (λz, z ∈ succ x ∧ z ∉ I),
	{
		apply @subclass_of_set_is_set (λz, z ∈ succ x ∧ z ∉ I) (succ x),
		intros y hy, exact hy.1,
	},
	cases temp with X hX, dsimp at hX,
	have X_nonempty : X ≠ ∅,
	{
		intro contra,
		specialize hX x,
		have := hX.mpr ⟨lt_succ_self x, h⟩,
		rw contra at this,
		exact (mem_empty x).mp this,
	},
	have X_ord_set : subset_class X ON,
	{
		intros y hyX,
		rw hX y at hyX,
		have := mem_of_nat_is_nat (succ_of_nat_is_nat x_nat) hyX.1,
		exact nonempty.intro (nat_is_ord this),
	},

	rcases ON_ordinal_class.wo.wf X_ord_set X_nonempty with ⟨n, hnX, hn_min⟩,
	have n_ord := ord_of_mem_ON (X_ord_set hnX),
	have n_nat : n ∈ nat,
	{
		rw hX n at hnX,
		have succ_ord := succ_of_nat_is_nat x_nat,
		exact mem_of_nat_is_nat succ_ord hnX.1,
	},
	have : n ≠ ∅ ∧ ¬is_successor n_ord,
	{
		split,
		{
			intro contra,
			rw contra at hnX,
			rw hX ∅ at hnX,
			exact hnX.2 hI.1,
		},
		{
			intro contra,
			rcases contra with ⟨m, m_ord, hm⟩,
			by_cases hmI : m ∈ I,
			{
				have := hI.2 hmI,
				rw← hm at this,
				rw hX n at hnX,
				exact hnX.2 this,
			},
			{
				have hmSm := lt_succ_self m,
				rw← hm at hmSm,
				have hSx_ord := nat_is_ord (succ_of_nat_is_nat x_nat),
				rw hX n at hnX,
				have := hSx_ord.tran hnX.1 hmSm,
				have hmX : m ∈ X,
				{
					rw hX m,
					exact ⟨this, hmI⟩,
				},
				exact (hn_min hmX) hmSm,
			},
		},
	},
	have contra := non_zero_nat_is_succ n_nat this.1,
	exact this.2 contra,
end

theorem inductive_set_contains_nat {I : Set} (hI : is_inductive I) : subclass_set nat I :=
begin 
	let φ : fclass := λx, x ∈ I,
	have hφ : inductive_class φ,
	{
		split,
		{exact hI.1},
		{
			intros y hy,
			exact hI.2 hy,
		},
	},
	exact inductive_class_contains_nat hφ
end

axiom infinity_axiom : ∃I, is_inductive I

theorem nat_is_set : is_set nat :=
begin 
	cases infinity_axiom with I hI,
	apply @subclass_of_set_is_set nat I,
	exact inductive_set_contains_nat hI,
end


def ω : Set := classical.some nat_is_set

lemma tran_set_of_ord_is_ord {x : Set} (x_tran : transitive x) (x_ords : subset_class x ON) : 
ordinal x := 
{
	tran := x_tran,
	wo := 
	{
		irrfl := λy hy, ON_ordinal_class.wo.irrfl (x_ords hy),
		tran := λa b c ha hb hc hab hbc, ON_ordinal_class.wo.tran 
		(x_ords ha) (x_ords hb) (x_ords hc) hab hbc,
		tri := λa b ha hb, ON_ordinal_class.wo.tri (x_ords ha) (x_ords hb),
		wf := λX hX1 hX2, ON_ordinal_class.wo.wf (λy hy, x_ords (hX1 hy)) hX2,
	}
}

@[simp]lemma mem_omega : ∀x, x ∈ ω ↔ x ∈ nat := classical.some_spec nat_is_set

theorem induction_set {I : Set} (hI : is_inductive I) (h : I ⊆ ω) : I = ω :=
begin 
	rw eq_iff_subsets,
	use h,
	have := inductive_set_contains_nat hI,
	intros n hn,
	simp at hn,
	exact this hn,
end

theorem induction_class {I : fclass} (hI : inductive_class I) (h : subclass_set I ω) : 
∃I_set : is_set I, set_of I_set = ω :=
begin 
	have I_set := subclass_of_set_is_set h,
	use I_set,
	have h1 : is_inductive (set_of I_set),
	{
		split,
		{
			simp,
			exact hI.1,
		},
		{
			simp,
			exact hI.2,
		},
	},
	have h2 : set_of I_set ⊆ ω,
	{
		intros x hx,
		simp at hx,
		exact h hx,
	},
	exact induction_set h1 h2,
end

theorem omega_ord : ordinal ω :=
begin 
	apply tran_set_of_ord_is_ord,
	{
		intros n hn m hm,
		rw mem_omega at *,
		exact mem_of_nat_is_nat hn hm,
	},
	{
		intros n hn,
		rw mem_omega at hn,
		exact nonempty.intro (nat_is_ord hn),
	}
end

lemma ord_contains_empty {x : Set} (x_ord : ordinal x) (x_nonempty : x ≠ ∅) : ∅ ∈ x :=
begin 
	rcases x_ord.wo.wf (subset_self x) x_nonempty with ⟨t, htx, t_min⟩,
	have h_inter : t ∩ x = ∅,
	{
		by_contra h,
		cases nonempty_has_mem h with a ha,
		simp at ha,
		exact t_min ha.2 ha.1,
	},
	have t_ss := x_ord.tran htx,
	by_cases contra : t = ∅,
	{rw← contra, exact htx,},
	{
		exfalso,
		cases nonempty_has_mem contra with a ha,
		have : a ∈ t ∩ x,
		{
			rw mem_pair_inter,
			exact ⟨ha, t_ss ha⟩,
		},
		rw h_inter at this,
		exact (mem_empty a).mp this,
	},
end

lemma lim_ordinal_is_inductive {x : Set} {x_ord : ordinal x} (x_lim : is_limit x_ord) :
 is_inductive x :=
 begin 
	 split,
	 {exact ord_contains_empty x_ord x_lim.1},
	 intros y hy,
	 have y_ord : ordinal y := mem_ord_is_ord x_ord hy,
	 cases ON_ordinal_class.wo.tri (mem_ON_of_ord x_ord) 
	 (mem_ON_of_ord (succ_of_ordinal_is_ordinal y_ord)),
	 {
		 rw mem_succ at h,
		 cases h,
		 {
			 exfalso,
			 exact not_ord_mem_ord x_ord h hy,
		 },
		 {
			 rw h at hy,
			 exfalso,
			 exact ord_not_mem_self (mem_ON_of_ord y_ord) hy,
		 },
	 },
	 cases h,
	 {exact h},
	 {
		 exfalso,
		 apply x_lim.2,
		 use [y, y_ord],
		 exact h,
	 }
 end

theorem ω_smallest_lim : is_limit omega_ord ∧ ∀⦃α⦄ (α_ord : ordinal α), is_limit α_ord → ω ≤ α :=
begin 
	split,
	{
		split,
		{
			intro h,
			have := empty_is_nat,
			rw← mem_omega at this,
			rw h at this,
			exact (mem_empty ∅).mp this,
		},
		{
			intro h,
			rcases h with ⟨x, x_ord, hx⟩,
			have x_nat : x ∈ nat,
			{
				have := lt_succ_self x,
				rw← hx at this,
				unfold has_lt.lt at this,
				rw mem_omega at this,
				exact this,
			},
			have sx_nat := succ_of_nat_is_nat x_nat,
			rw← hx at sx_nat,
			rw← mem_omega at sx_nat,
			exact ord_not_mem_self (mem_ON_of_ord omega_ord) sx_nat,
		},
	},
	{
		intros α α_ord h,
		rw ← le_iff_subset (mem_ON_of_ord omega_ord) (mem_ON_of_ord α_ord),
		have := lim_ordinal_is_inductive h,
		intros n hn,
		simp at hn,
		exact inductive_set_contains_nat this hn,
	}
end

lemma sing_is_pair (x : Set) : pair_set x x = sing x := rfl
lemma sing_eq (x y : Set) : sing x = sing y ↔ x = y := 
begin 
	split,
	{
		intro h,
		have : x ∈ sing x := (mem_sing x x).mpr rfl,
		rw h at this,
		simp at this,
		exact this,
	},
	{
		exact congr_arg (λ (x : Set), sing x),
	},
end

lemma mem_pair_fst (a b : Set) : a ∈ pair_set a b :=
begin 
	rw mem_pair,
	exact or.inl rfl,
end

lemma mem_pair_snd (a b : Set) : b ∈ pair_set a b :=
begin 
	rw mem_pair,
	exact or.inr rfl,
end

def ord_pair (x y : Set) := pair_set (sing x) (pair_set x y)

lemma ord_pair_eq {x y a b : Set} : ord_pair x y = ord_pair a b → x = a ∧ y = b := 
begin 
	unfold ord_pair,

	intro h,
	by_cases hxy : x = y,
	{
		rw← hxy at h,
		rw sing_is_pair at h,
		rw sing_is_pair at h,
		have hx : sing x ∈ pair_set (sing a) (pair_set a b),
		{rw← h, simp},
		simp at hx,
		cases hx,
		{
			rw sing_eq at hx,
			use hx,
			have : (pair_set a b) ∈ sing (sing x),
			{rw h, rw mem_pair, exact or.inr rfl},
			simp at this,
			rw hx at this,
			have hb := mem_pair_snd a b,
			rw this at hb,
			rw mem_sing at hb,
			exact (eq.congr hxy (eq.symm hb)).mp hx,
		},
		{
			have ha := mem_pair_fst a b,
			rw← hx at ha,
			rw mem_sing at ha,
			use ha.symm,

			have hb := mem_pair_snd a b,
			rw ← hx at hb,
			rw mem_sing at hb,
			exact (rfl.congr (eq.symm hb)).mp (eq.symm hxy),
		},
	},
	{
		have hxa : x = a,
		{
			have hx := mem_pair_fst (sing x) (pair_set x y),
			rw h at hx, simp at hx,
			cases hx,
			{exact (sing_eq x a).mp hx},
			{
				have := mem_pair_fst a b,
				rw← hx at this, simp at this,
				exact this.symm,
			},
		},
		use hxa,

		have temp := mem_pair_snd (sing x) (pair_set x y),
		rw h at temp, simp at temp,
		cases temp,
		{
			exfalso,
			have := mem_pair_snd x y,
			rw temp at this, simp at this,
			finish,
		},
		{
			have := mem_pair_snd x y,
			rw temp at this, simp at this,
			cases this,
			{exfalso,finish},
			{exact this},
		},
	}
end

lemma ord_pair_eq_iff (x y a b : Set) : 
ord_pair x y = ord_pair a b ↔ x = a ∧ y = b := 
⟨ord_pair_eq, λh, congr (congr_arg ord_pair h.1) h.2⟩

def is_ord_pair (x : Set) : Prop := ∃a b, x = ord_pair a b

def is_set_relation (x : Set) : Prop := ∀⦃y⦄, y ∈ x → is_ord_pair y
def is_set_function (x : Set) : Prop := ∀⦃y⦄, y ∈ x → ∃b a, y = ord_pair a b ∧ ∀⦃c⦄,
 ord_pair a c ∈ x → b = c

def is_class_function (φ : relation) : Prop := ∀x, ∃y, φ x y ∧ ∀⦃z⦄, φ x z → y = z
def is_class_function_on_set (φ : relation) (X : Set) : Prop :=
 ∀⦃x⦄, x ∈ X → ∃y , φ x y ∧ ∀⦃z⦄, φ x z → y = z

 structure set_function (f : Set) :=
 (is_func : is_set_function f)

attribute [class] set_function

structure class_function (φ : relation) :=
(is_func : is_class_function φ)

structure class_function_on_set (φ : relation) (X : Set) :=
(is_func : is_class_function_on_set φ X)

attribute [class] class_function
attribute [class] class_function_on_set

lemma set_func_of_is_set_func {f : Set} (hf : is_set_function f) : set_function f :=
{is_func := hf}
lemma class_func_of_is_class_func {φ : relation} 
(hφ : is_class_function φ) : class_function φ := {is_func := hφ}
lemma class_on_set_func_of_is_class_func {φ : relation} {X : Set}
(hφ : is_class_function_on_set φ X) : class_function_on_set φ X := {is_func := hφ}


axiom replacement_axiom (φ : relation) [class_function φ] (A : Set) : 
∃B : Set, ∀⦃y⦄, (∃⦃z⦄ (hz : z ∈ A), φ z y) → y ∈ B

lemma replacement' (φ : relation) [φ_func : class_function φ] (A : Set) : 
∃B : Set, ∀y, (∃z (hz : z ∈ A), φ z y) ↔ y ∈ B :=
begin
	cases replacement_axiom φ A with B hB,

	let P := λx, (∃⦃z⦄ (hz : z ∈ A), φ z x),
	have hP : subclass_set P B,
	{
		intros t ht,
		apply hB,
		rcases ht with ⟨z, hz1, hz2⟩,
		use z,
		exact ⟨hz1, hz2⟩,
	},

	cases (subclass_of_set_is_set hP) with C hC,
	use C,
	intro y,
	rw hC y,
end

lemma domain_exists (x : Set) : ∃D : Set, ∀z, z ∈ D ↔ (∃b, ord_pair z b ∈ x) :=
begin 
	let φ := λn m, (∃b, n = ord_pair m b) ∨ (¬is_ord_pair n ∧ m = ∅),
	have φ_func : is_class_function φ,
	{
		intros n,
		by_cases is_ord_pair n,
		{
			rcases h with ⟨m, b, hmb⟩,
			use m,
			split,
			{
				left,
				use b,
				exact hmb,
			},
			{
				intros m' hm',
				cases hm',
				{
					cases hm' with b' hb',
					rw hb' at hmb,
					exact (ord_pair_eq hmb).1.symm,
				},
				{
					exfalso, 
					apply hm'.1,
					use [m, b],
					exact hmb,
				},
			},
		},
		{
			use ∅,
			split,
			{
				right,
				use h,
			},
			{
				intros z hz,
				cases hz,
				{
					exfalso,
					cases hz with b hb,
					apply h,
					use [z, b],
					exact hb,
				},
				{
					exact hz.2.symm,
				},
			},
		},
	},
	have φ_inst := class_function.mk φ_func,
	have := @replacement_axiom φ φ_inst x,
	
	let P := λz, ∃ (b : Set), ord_pair z b ∈ x,
	cases this with B hB,
	have hP : subclass_set P B,
	{
		intros y hy,
		apply hB,
		cases hy with t ht,
		use ord_pair y t, use ht,
		finish,
	},
	cases (subclass_of_set_is_set hP) with D hD,
	use D,
	finish,
end

def domain (x : Set) : Set := classical.some (domain_exists x)
@[simp]lemma mem_domain (y x : Set) : y ∈ domain x ↔ ∃ (b : Set), ord_pair y b ∈ x
:= classical.some_spec (domain_exists x) y

lemma mem_domain_pair {x y f : Set} (hxyf : ord_pair x y ∈ f ) : x ∈ domain f :=
begin 
	rw mem_domain,
	use [y, hxyf],
end

lemma inv_exists (X : Set) : 
∃I : Set, ∀m, m ∈ I ↔ ∃n a b, (n ∈ X ∧ n = ord_pair a b ∧ m = ord_pair b a) :=
begin 
	let φ := λn m, (∃a b, n = ord_pair a b ∧
	m = ord_pair b a) ∨ (¬is_ord_pair n ∧ m = ∅),

	have φ_is_func : is_class_function φ,
	{
		intros n,
		by_cases is_ord_pair n,
		{
			rcases h with ⟨a, b, hab⟩,
			use ord_pair b a,
			split,
			{
				left,
				use [a, b],
				exact ⟨hab, rfl⟩,
			},
			{
				intros m' hm',
				cases hm',
				{
					rcases hm' with ⟨a', b', hab'⟩,
					rw hab'.1 at hab,
					rw hab'.2,
					rw ord_pair_eq_iff at *,
					tauto,
				},
				{
					exfalso,
					apply hm'.1,
					use [a, b],
					exact hab,
				},
			},
		},
		{
			use ∅,
			split,
			{right, use h,},
			{
				intros m hm,
				cases hm,
				{
					exfalso,
					apply h,
					rcases hm with ⟨a, b, hab⟩,
					use [a, b],
					exact hab.1,
				},
				{exact hm.2.symm,},
			},
		},
	},

	have := @replacement_axiom φ (class_function.mk φ_is_func) X,
	
	let P := λm, ∃ (n a b : Set), n ∈ X ∧ n = ord_pair a b ∧ m = ord_pair b a,
	cases this with B hB,
	have hP : subclass_set P B,
	{
		intros m hm,
		apply hB,
		rcases hm with ⟨x, a, b, hx⟩,
		use ord_pair a b,
		split,
		{finish},
		{
			left,
			finish,
		},
	},
	cases (subclass_of_set_is_set hP) with I hI,
	use I,
	exact hI,
end

def inv (x : Set) : Set := classical.some (inv_exists x)
@[simp]lemma mem_inv (y x : Set) : 
y ∈ inv x ↔ ∃ (n a b : Set), n ∈ x ∧ n = ord_pair a b ∧ y = ord_pair b a :=
classical.some_spec (inv_exists x) y

def range (x : Set) : Set := domain (inv x)
@[simp]lemma mem_range (y x : Set) : y ∈ range x ↔ ∃a, ord_pair a y ∈ x :=
begin 
	unfold range,
	simp,
	split,
	{
		intro h,
		rcases h with ⟨b, n, hn, c, d, hcd⟩,
		use c,
		suffices hn2 : n = ord_pair c y,
		{
			rw← hn2,
			exact hn,
		},
		{
			rw hcd.1,
			rw ord_pair_eq_iff at *,
			use rfl,
			finish,
		},
	},
	{
		intro h,
		cases h with a ha,
		use [a, ord_pair a y, ha, a, y, rfl],
	},
end

lemma eval_exists (f : Set) {x : Set} [set_function f] (hx : x ∈ domain f) :
∃(y : Set) (hy : y ∈ range f), ord_pair x y ∈ f :=
begin 
	rw mem_domain at hx,
	cases hx with y hy,
	use y,
	simp,
	split,
	{
		use x,
		exact hy,
	},
	{exact hy},
end

def eval (f : Set) {x : Set} [set_function f] (hx : x ∈ domain f)  := 
classical.some (eval_exists f hx)

lemma eval_spec (f : Set) {x : Set} [set_function f] (hx : x ∈ domain f) 
: ∃(hy : eval f hx ∈ range f), ord_pair x (eval f hx ) ∈ f :=
classical.some_spec (eval_exists f hx)

lemma eval_unique (f : Set) {x : Set} [set_function f] (hx : x ∈ domain f)  {y : Set} :
ord_pair x y ∈ f → y = eval f hx := 
begin
	intro h,
	cases eval_spec f hx with hord hpair,
	rcases _inst_1.is_func hpair with ⟨b, a, hab⟩,
	rw ord_pair_eq_iff at hab,
	cases hab,
	rw← hab_left.1 at hab_right,
	rw← hab_left.2 at hab_right,
	exact (hab_right h).symm,
end

lemma eval_behaves (f : Set) {x : Set} [set_function f] (hx1 : x ∈ domain f) 
(hx2 : x ∈ domain f) : eval f hx1 = eval f hx2 :=
begin 
	have h1 := eval_spec f hx1,
	have h2 := eval_spec f hx2,
	cases h1 with y1 hy1,
	cases h2 with y2 hy2,
	exact eval_unique f hx1 hy1,
end

lemma mem_range_iff_eval (f : Set) [set_function f] : ∀⦃y⦄, y ∈ range f ↔
 ∃(x : Set) (hx : x ∈ domain f), y = eval f hx :=
begin 
	intro y,
	split,
	{
		intro h,
		simp at h,
		cases h with a ha,
		use a,
		have haf : a ∈ domain f,
		{
			simp,
			use y,
			exact ha,
		},
		use haf,
		apply eval_unique f haf ha,
	},
	{
		intro h,
		simp,
		rcases h with ⟨a, haf, ha⟩,
		use a,
		rw mem_domain at haf,
		cases haf with b hb,
		rw ha,
		cases eval_spec f haf with heval,
		exact h,
	},
end

def injective (f : Set) := 
∀⦃x x' y⦄, 
ord_pair x y ∈ f → ord_pair x' y ∈ f → x = x'

lemma injective_iff_bad (f : Set) [set_function f] : injective f ↔ ∀⦃x y⦄ 
{hxf : x ∈ domain f} {hyf : y ∈ domain f}, eval f hxf = eval f hyf →
x = y :=
begin 
	split,
	{
		intros h x y hxf hyf hf,
		cases eval_spec f hxf with hf1 hf2,
		cases eval_spec f hyf with hf3 hf4,
		rw← hf at hf4,
		exact h hf2 hf4,
	},
	{
		intros h x x' y hxy hxy',
		have hxf := mem_domain_pair hxy,
		have hxf' := mem_domain_pair hxy',
		have := eval_unique f hxf' hxy',
		rw eval_unique f hxf hxy at this,
		exact h this,
	},
end

structure full_func (f : Set) extends set_function f :=
(codomain : Set)
(h_codomain : range f ⊆ codomain)

attribute [class] full_func

def surjective (f : Set) [f_func : full_func f] := f_func.codomain ⊆ range f

lemma surjective_iff_eq {f : Set} [f_func : full_func f] : 
surjective f ↔ f_func.codomain = range f :=
begin 
	split,
	{
		rw eq_iff_subsets,
		intro h,
		use h,
		exact f_func.h_codomain,
	},
	{
		intro h,
		unfold surjective,
		rw h,
		exact subset_self (range f),
	},
end

lemma inv_of_inj_is_func {f : Set} (f_func : set_function f)
(f_inj : injective f) : set_function (inv f) :=
begin
	rw injective_iff_bad at f_inj,
	apply set_func_of_is_set_func,
	intros p hp,
	rw mem_inv at hp,
	rcases hp with ⟨n, a, b, hn⟩,
	use [a, b],
	split,
	{
		rw hn.2.2,
	},
	{
		intros c hc,
		rw mem_inv at hc,
		rcases hc with ⟨m, a', b', hm⟩,
		rw ord_pair_eq_iff at hm,
		rcases hm with ⟨hm1, hm2, hm3⟩,
		rw [←hm3.1, ←hm3.2] at hm2,
		rw hm2 at hm1,
		rcases hn with ⟨hn1, hn2, hn3⟩,
		rw hn2 at hn1,
		have haf : a ∈ domain f,
		{
			rw mem_domain,
			use [b, hn1],
		},
		have hcf : c ∈ domain f,
		{
			rw mem_domain,
			use [b, hm1],
		},
		have hba := eval_unique f haf hn1,
		have hbc := eval_unique f hcf hm1,
		rw hba at hbc,
		exact f_inj hbc,
	},
end

lemma restricted_replacement {φ : relation} {X : Set} (φ_func : class_function_on_set φ X) :
∃B : Set, ∀z, z ∈ B ↔ ∃x ∈ X, φ x z := 
begin 
	let P := λ x y, (x ∈ X ∧ φ x y) ∨ (x ∉ X ∧ y = ∅),
	have P_func : is_class_function P,
	{
		intro x,
		by_cases hx : x ∈ X,
		{
			cases φ_func.is_func hx with y hy,
			use y,
			split,
			{
				left,
				use [hx, hy.1],
			},
			{
				intros y' hy',
				cases hy',
				{exact hy.2 hy'.2},
				{finish},
			},
		},
		{
			use ∅,
			split,
			{
				right,
				use hx,
			},
			{
				intros z hz,
				cases hz,
				{finish},
				{finish},
			},
		},
	},

	cases @replacement_axiom P ({is_func := P_func}) X with C hC,
	have h_subclass : subclass_set (λ z, ∃ (x : Set) (H : x ∈ X), φ x z) C := 
	by finish,

	cases subclass_of_set_is_set h_subclass with B hB,
	use B,
	exact hB,
end


lemma prod_exists (A B : Set) : ∃C : Set, ∀p, p ∈ C ↔
 ∃a b, a ∈ A ∧ b ∈ B ∧ p = ord_pair a b :=
begin 
	have lem_1 : ∀⦃a⦄, a ∈ A → ∃ D : Set, ∀p, p ∈ D ↔ ∃b, b ∈ B ∧ p = ord_pair a b,
	{
		intros a ha,
		let φ := λx y, y = ord_pair a x,
		have φ_func : is_class_function_on_set φ B,
		{
			intros x hx,
			use ord_pair a x,
			split,
			{exact rfl,},
			{exact λ {b : Set}, eq_comm.mpr},
		},

		cases restricted_replacement {is_func := φ_func} with D hD,
		use D,
		finish,
	},
	let φ := λx y, ∀p, p ∈ y ↔ ∃b, b ∈ B ∧ p = ord_pair x b,
	have φ_func : is_class_function_on_set φ A,
	{
		intros a ha,
		cases lem_1 ha with y hy,
		use y,
		split,
		{exact hy},
		{
			intros z hz,
			ext,
			exact iff.trans (hy z_1) (iff.symm (hz z_1)),
		},
	},
	cases restricted_replacement {is_func := φ_func} with F hF,
	use union F,
	simp,
	intros p,
	split,
	{
		intro h,
		cases h with Y hY,
		rw hF at hY,
		cases hY with temp hpY,
		rcases temp with ⟨a, ha, hφa⟩,
		use [a, ha],
		rw hφa p at hpY,
		cases hpY with x hx,
		use [x, hx.1, hx.2],
	},
	{
		intro h,
		rcases h with ⟨a, haA, b, hbB, hbp⟩,
		cases lem_1 haA with Y hY,
		use Y,
		split,
		{
			rw hF,
			use [a, haA],
			exact hY,
		},
		{
			rw hY,
			use [b, hbB, hbp],
		},
	},
end

def prod (A B : Set) := classical.some (prod_exists A B)

infix ` × ` :72 := prod

lemma mem_prod (A B : Set) : ∀p, p ∈ A × B ↔ ∃a b, a ∈ A ∧ b ∈ B ∧ p = ord_pair a b
:= classical.some_spec (prod_exists A B)

lemma mem_prod_pair (a b A B : Set) : ord_pair a b ∈ A × B ↔ a ∈ A ∧ b ∈ B :=
begin 
	rw mem_prod,
	split,
	{
		intro h,
		rcases h with ⟨x, y, hxy⟩,
		rw ord_pair_eq_iff at hxy,
		finish,
	},
	{
		intro h,
		use [a, b, h.1, h.2],
	},
end

def set_restriction (f A : Set) := 
classical.some (specification_axiom f (λx, ∃a b, a ∈ A ∧ x = ord_pair a b))

lemma mem_restriction (f A : Set) :
 ∀x, x ∈ set_restriction f A ↔ x ∈ f ∧ ∃a b, a ∈ A ∧ x = ord_pair a b :=
classical.some_spec (specification_axiom f (λx, ∃a b, a ∈ A ∧ x = ord_pair a b))

lemma is_func_restriction {f : Set} (f_func : set_function f) (A : Set) :
 set_function (set_restriction f A) := 
begin
	apply set_func_of_is_set_func,
	intros x hx,
	rw mem_restriction at hx,
	rcases hx with ⟨hxf, a, b, hab⟩,
	use [b, a, hab.2],
	intros c hc,
	rw mem_restriction at hc,
	rw hab.2 at hxf,
	rcases f_func.is_func hxf with ⟨c', a', hac1, hac2⟩,
	rw ord_pair_eq_iff at hac1,
	rw hac1.1 at hc,
	rw hac1.2,
	exact hac2 hc.1,
 end

def comp (g f : Set) := 
classical.some (specification_axiom ((domain f) × range g) 
(λp, ∃x y z, p = ord_pair x z ∧ ord_pair x y ∈ f ∧ ord_pair y z ∈ g))

infix ` ∘ ` := comp

lemma mem_comp' (g f : Set) : 
∀p, p ∈ g ∘ f ↔ p ∈ (domain f × range g) ∧
∃x y z, p = ord_pair x z ∧ ord_pair x y ∈ f ∧ ord_pair y z ∈ g := classical.some_spec
(specification_axiom ((domain f) × range g) 
(λp, ∃x y z, p = ord_pair x z ∧ ord_pair x y ∈ f ∧ ord_pair y z ∈ g))

@[simp]lemma mem_comp (g f : Set) : ∀p, p ∈ g ∘ f ↔ ∃x y z, p = ord_pair x z ∧
ord_pair x y ∈ f ∧ ord_pair y z ∈ g :=
begin 
	intro p,
	rw [mem_comp', mem_prod],
	split,
	{
		intro h,
		cases h with h1 h2,
		rcases h2 with ⟨x, y, z, hxyz⟩,
		rcases h1 with ⟨a, b, hab⟩,
		rw hab.2.2 at hxyz,
		rw ord_pair_eq_iff at hxyz,
		rw hxyz.1.1 at hab,
		rw hxyz.1.2 at hab,
		use [x, y, z, hab.2.2, hxyz.2.1, hxyz.2.2],
	},
	{
		intro h,
		rcases h with ⟨x, y, z, hp⟩,
		use [x, z],
		rw mem_domain,
		rw mem_range,
		use [y, hp.2.1, y, hp.2.2, hp.1],
		use [x, y, z, hp],
	},
end

lemma mem_comp_pair (g f : Set) : ∀x z, ord_pair x z ∈ g ∘ f ↔ 
∃y, ord_pair x y ∈ f ∧ ord_pair y z ∈ g :=
begin
	intros x z,
	rw mem_comp,
	split,
	{
		intro h,
		rcases h with ⟨x', y, z', hp1, hp2⟩,
		rw ord_pair_eq_iff at hp1,
		rw← hp1.1 at hp2,
		rw← hp1.2 at hp2,
		use [y, hp2],
	},
	{
		intro h,
		cases h with y hy,
		use [x, y, z, rfl, hy],
	},
end

lemma func_out_unique {f : Set} [set_function f] {x y y' : Set} (hxy : ord_pair x y ∈ f)
(hxy' : ord_pair x y' ∈ f) : y = y' := 
begin
	have h := _inst_1.is_func hxy,
	rcases h with ⟨b, a, h1, h2⟩,
	rw ord_pair_eq_iff at h1,
	rw [←h1.1, ←h1.2] at h2,
	exact h2 hxy',
end

lemma comp_is_func {g f : Set} (g_func :set_function g) (f_func : set_function f) :
set_function (g ∘ f) :=
begin 
	apply set_func_of_is_set_func,
	intros p hp,
	rw mem_comp at hp,
	rcases hp with ⟨x, y, z, hp, hxyf,  hyzg⟩,
	use [z, x, hp],
	intros z' hz',
	rw mem_comp_pair at hz',
	cases hz' with y' hy',
	have := func_out_unique hxyf hy'.1,
	rw← this at hy',
	exact func_out_unique hyzg hy'.2,
end

lemma domain_of_comp_bad (g f : Set) [set_function g] [set_function f]  : 
domain (g ∘ f) = { x ∈ domain f | ∃hx : x ∈ domain f, eval f hx ∈ domain g} :=
begin 
	ext x,
	split,
	{
		intro h,
		rw mem_domain at h,
		cases h with z hz,
		rw mem_sep,
		rw mem_comp_pair at hz,
		cases hz with y hy,
		have hx : x ∈ domain f,
		{
			rw mem_domain,
			use [y, hy.1],
		},
		use [hx, hx],
		rw← eval_unique f hx hy.1,
		exact mem_domain_pair hy.2,
	},
	{
		intro h,
		rw mem_domain,
		rw mem_sep at h,
		rcases h with ⟨hx2, hx, hgx⟩,
		rw mem_domain at hgx,
		cases hgx with z hz,
		use z,
		rw mem_comp,
		use [x, (eval f hx), z, rfl],
		split,
		{
			cases eval_spec f hx with y hy,
			exact hy,
		},
		{
			exact hz,
		},
	},
end


structure set_relation (r : Set) :=
(is_rel : is_set_relation r)

attribute [class] set_relation

def set_reflexive (r : Set) := 
∀⦃a⦄, a ∈ domain r → ord_pair a a ∈ r 

def set_symmetric (r : Set) := 
∀⦃a b⦄, a ∈ domain r → b ∈ domain r → ord_pair a b ∈ r → ord_pair b a ∈ r

def set_transitive (r : Set) := 
∀⦃a b c⦄, a ∈ domain r → b ∈ domain r → c ∈ domain r → ord_pair a b ∈ r → 
ord_pair b c ∈ r → ord_pair a c ∈ r

structure set_equiv_relation (r : Set) extends set_relation r := 
(refl : set_reflexive r)
(symm : set_symmetric r)
(tran : set_transitive r)

attribute [class] set_equiv_relation
attribute [class] ordinal


def func_of_set_function (f : Set) [set_function f] : Set → Set := 
begin 
	intro x,
	by_cases x ∈ domain f,
	exact eval f h,
	exact ∅,
end

lemma pair_union_ordinal {a b : Set} (ha : ordinal a) (hb : ordinal b) : ordinal (a ∪ b) :=
begin 
	by_cases a ≤ b,
	{
		suffices : a ∪ b = b,
		{
		rw this,
		exact hb,
		},

		unfold has_le.le at h,
		cases h,
		{
			have ha_ss := hb.tran h,
			ext x,
			rw mem_pair_union,
			split,
			{
				intro hx,
				cases hx,
				exact ha_ss hx,
				exact hx,
			},
			{
				intro hx,
				right,
				exact hx,
			},
		},
		{
			ext x,
			rw← h,
			split,
			{
				intro hx,
				rw mem_pair_union at hx,
				cases hx,
				exact hx,

				exact hx,
			},
			{
				intro h,
				rw mem_pair_union,
				exact or.inl h,
			},
		},
	},
	have hba : b ∈ a,
	{
		cases ON_ordinal_class.wo.tri (mem_ON_of_ord ha) (mem_ON_of_ord hb),
		{
			exfalso, apply h,
			unfold has_le.le,
			left, exact h_1,
		},
		{
			cases h_1, exact h_1,
			exfalso,
			apply h,
			unfold has_le.le,
			right, exact h_1,
		},
	},
	have hb_ss := ha.tran hba,
	suffices : a ∪ b = a,
	{rw this, exact ha,},
	ext x,
	rw mem_pair_union,
	split,
	{
		intro hx,
		cases hx,
		exact hx,
		exact hb_ss hx,
	},
		{
		intro hx,
		left,
		exact hx,
	},
end

lemma union_ordinal {F : Set} (hF : subset_class F ON) : ordinal (union F) :=
begin 
	fconstructor,
	{
		intros a ha b hb,
		rw mem_union at *,
		rcases ha with ⟨Y, hY, ha⟩,
		use [Y, hY],
		have Y_ord := ord_of_mem_ON (hF hY),
		exact Y_ord.tran ha hb,
	},
	{
		fconstructor,
		{
			intros a haF ha,
			rw mem_union at haF,
			rcases haF with ⟨Y, hY, haY⟩,
			have Y_ord := ord_of_mem_ON (hF hY),
			have a_ord := mem_of_ordinal_is_ordinal (hF hY) haY,
			exact ord_not_mem_self a_ord ha,
		},
		{
			intros a b c ha hb hc hab hbc,
			rw mem_union at *,
			rcases ha with ⟨Y1, hY1, haY1⟩,
			rcases hb with ⟨Y2, hY2, hbY2⟩,
			rcases hc with ⟨Y3, hY3, hcY3⟩,

			have Y1_ord := ord_of_mem_ON (hF hY1),
			have Y2_ord := ord_of_mem_ON (hF hY2),
			have Y3_ord := ord_of_mem_ON (hF hY3),
			let Y := Y1 ∪ Y2 ∪ Y3,
			have Y_ord := pair_union_ordinal (pair_union_ordinal Y1_ord Y2_ord) (Y3_ord),
			have haY : a ∈ Y,
			{
				rw mem_pair_union,
				rw mem_pair_union,
				left, left, exact haY1,
			},
			have hbY : b ∈ Y,
			{
				rw mem_pair_union,
				rw mem_pair_union,
				left, right, exact hbY2,
			},
			have hcY : c ∈ Y,
			{
				rw mem_pair_union,
				rw mem_pair_union,
				right, exact hcY3,
			},
			exact Y_ord.wo.tran haY hbY hcY hab hbc,
		},
		{
			intros a b ha hb,
			rw mem_union at *,

			rcases ha with ⟨Y1, hY1, haY1⟩,
			rcases hb with ⟨Y2, hY2, hbY2⟩,

			have Y1_ord := ord_of_mem_ON (hF hY1),
			have Y2_ord := ord_of_mem_ON (hF hY2),

			let Y := Y1 ∪ Y2,
			have Y_ord := pair_union_ordinal Y1_ord Y2_ord,
			have haY : a ∈ Y,
			{
				rw mem_pair_union,
				left, exact haY1,
			},
			have hbY : b ∈ Y,
			{
				rw mem_pair_union,
				right, exact hbY2,
			},

			exact Y_ord.wo.tri haY hbY,
		},
		{
			intros X hX hXF,
			have X_ord_class : subset_class X ON,
			{
				intros a haX,
				specialize hX haX,
				rw mem_union at hX,
				rcases hX with ⟨Y, hY, haY⟩,
				specialize hF hY,
				exact mem_of_ordinal_is_ordinal hF haY,
			},
			exact ON_ordinal_class.wo.wf X_ord_class hXF,
		},
	},
end

lemma ord_not_le {a b : Set} [ordinal a] [ordinal b] (h: ¬a ≤ b) : b ∈ a :=
begin 
	unfold has_le.le at h,
	push_neg at h,
	have := ON_ordinal_class.wo.tri (mem_ON_of_ord _inst_1) (mem_ON_of_ord _inst_2),
	finish,
end

lemma union_is_sup (F : Set) (hF : subset_class F ON) : (∀⦃Y⦄, Y ∈ F → Y ≤ union F) ∧ 
∀(S : Set) [ordinal S], (∀⦃Y⦄, Y ∈ F → Y ≤ S) → union F ≤ S :=
begin 
	have U_ord := mem_ON_of_ord (union_ordinal hF),

	split,
	{
		intros Y hY,
		have Y_ord := hF hY,
		rw← le_iff_subset Y_ord U_ord,
		intros x hx,
		rw mem_union,
		use [Y, hY, hx],
	},
	{
		intros S S_ord hS,
		rw← le_iff_subset U_ord (mem_ON_of_ord S_ord),
		intros A hA,
		rw mem_union at hA,
		rcases hA with ⟨Y, hYF, hAY⟩,
		specialize hS hYF,
		have Y_ord := hF hYF,
		rw← le_iff_subset Y_ord (mem_ON_of_ord S_ord) at hS,
		exact hS hAY,
	},
end

axiom powerset_axiom : ∀x : Set, ∃P : Set, ∀⦃y⦄, y ⊆ x → y ∈ P

lemma powerset_exits : ∀x : Set, ∃P : Set, ∀⦃y⦄, y ∈ P ↔ y ⊆ x :=
begin 
	intro x,
	cases powerset_axiom x with bigP hbigP,
	cases specification_axiom bigP (λy, y ⊆ x) with P hP,
	use P,
	simp at *,
	intros y,
	split,
	{
		intros h,
		specialize hP y,
		rw hP at h,
		exact h.2,
	},
	{
		intro h,
		specialize hbigP h,
		specialize hP y,
		rw hP,
		exact ⟨hbigP, h⟩,
	},
end

def powerset (x : Set) := classical.some (powerset_exits x)

prefix `𝒫 ` := powerset

@[simp] def mem_powerset (x : Set) : 
∀y, y ∈ 𝒫 x ↔ y ⊆ x := classical.some_spec (powerset_exits x)

structure bijection (f A B : Set) :=
[f_func : set_function f]
(f_domain : domain f = A)
(f_range : range f = B)
(f_injective : injective f)

def eval_class (φ : relation) [φ_func : class_function φ] (x : Set) := 
classical.some (φ_func.is_func x)

infix ` @@ `:1000 := eval_class

lemma func_class_spec {φ : relation} (φ_func : class_function φ) (x : Set)
: φ x (φ @@ x) ∧ ∀ {z : Set}, φ x z → (φ @@ x = z) := 
classical.some_spec (φ_func.is_func x)

lemma func_class_unique {φ : relation} (φ_func : class_function φ) : 
∀x y, φ x y ↔ φ @@ x = y :=
begin 
	intros x y,
	split,
	{
		intro h,
		cases func_class_spec φ_func x with hφx h2,
		exact h2 h,
	},
	{
		intro h,
		cases func_class_spec φ_func x with hφx h2,
		rcases φ_func.is_func x with ⟨y', hy', hu⟩,
		specialize hu hφx,
		rw← hu at h,
		rwa h at hy',
	},
end

def class_restriction (φ : relation) [φ_func : class_function φ] 
(A : Set) := {p ∈ A | ∃b a, p = ord_pair a b ∧ φ a b}

def class_injective_at {φ : relation} (φ_func : class_function φ) (F : fclass)
: Prop :=  ∀⦃x x'⦄, x ∈ F → x' ∈ F → φ @@ x = φ @@ x' → x = x'

lemma class_injective_at_iff (φ : relation) (φ_func : class_function φ) (F : fclass) :
class_injective_at φ_func F ↔ ∀⦃x x' y⦄, x ∈ F → x' ∈ F → φ x y → φ x' y → x = x' :=
begin 
	split,
	{
		intros h x x' y hxF hx'F hxy hx'y,
		rw func_class_unique φ_func at hxy hx'y,
		rw← hx'y at hxy,
		exact h hxF hx'F hxy,
	},
	{
		intros h x x' hxF hx'F hxx',
		have hx := func_class_spec φ_func x, 
		have hx' := func_class_spec φ_func x', 
		have := h hxF hx'F hx.1,
		rw hxx' at this,
		exact this hx'.1,
	},
end

def class_injection {φ : relation} (φ_func : class_function φ) : Prop :=
 ∀⦃x x'⦄, φ @@ x = φ @@ x' → x = x'

lemma class_injection_iff (φ : relation) (φ_func : class_function φ) :
class_injection φ_func ↔ ∀⦃x x' y⦄, φ x y → φ x' y → x = x' :=
begin 
	split,
	{
		intros h x x' y hxy hx'y,
		rw func_class_unique φ_func at hxy hx'y,
		rw← hx'y at hxy,
		exact h hxy,
	},
	{
		intros h x x' hxx',
		have h1 := func_class_spec φ_func x,
		have h2 := func_class_spec φ_func x',
		rw← hxx' at h2,
		exact h h1.1 h2.1,
	},
end

lemma class_injection_iff_univ {φ : relation} (φ_func : class_function φ) : 
class_injection φ_func ↔ class_injective_at φ_func univ :=
begin 
	split,
	{
		intros h x x' hx hx' hxx',
		exact h hxx',
	},
	{
		intros h x x' hxx',
		have := @h x x' _ _ hxx',
		{exact this},
		unfold has_mem.mem,
		unfold has_mem.mem,
	},
end

def class_range (φ : relation) : fclass := λy, ∃x, φ x y

lemma mem_class_range {φ : relation} (φ_func : class_function φ) :
 ∀y, y ∈ class_range φ ↔ ∃x, y = φ @@ x :=
 begin 
	 intros y,
	 unfold class_range has_mem.mem mem_class,
	 split,
	 {
		 intro hy,
		 cases hy with x hx,
		 use x,
		 rw func_class_unique φ_func x y at hx,
		 exact eq.symm hx,
	 },
	 {
		 intro h,
		 cases h with x hx,
		 use x,
		 rw hx,
		 exact (func_class_spec φ_func x).1,
	 },
 end

 structure class_function_on_class (φ : relation) (F : fclass) :=
 (is_func :  ∀⦃x⦄, x ∈ F → ∃y , φ x y ∧ ∀⦃z⦄, φ x z → y = z)

def class_inv (φ : relation) : relation := λx y, φ y x
lemma class_inv_of_inj {φ : relation} {φ_func : class_function φ}
(φ_inj : class_injection φ_func) : 
class_function_on_class (class_inv φ) (class_range φ) :=
begin 
	fconstructor,
	intros y hyF,
	rw mem_class_range φ_func at hyF,
	cases hyF with x hx,
	use x,
	unfold class_inv,
	rw hx,
	have := (func_class_spec φ_func x),
	use this.1,
	intros z hz,
	have hyF : y ∈ class_range φ,
	{
		rw mem_class_range φ_func,
		use [x, hx],
	},

	rw class_injection_iff at φ_inj,
	exact φ_inj this.1 hz,
end

def class_range_at (φ : relation) (F : fclass) : fclass := λy, ∃x ∈ F, φ x y
lemma class_range_at_univ (φ : relation) : 
∀y, class_range φ y ↔ class_range_at φ univ y :=
begin 
	intro y,
	unfold has_mem.mem class_range class_range_at,
	simp,
	unfold has_mem.mem mem_class univ,
	simp,
end

lemma mem_class_mem_at {φ : relation} (φ_func : class_function φ) (F : fclass) :
∀y, y ∈ class_range_at φ F ↔ ∃x ∈ F, φ @@ x = y :=
begin 
	intro y,
	split,
	unfold class_range_at has_mem.mem mem_class,
	{
		intro h,
		rcases h with ⟨x, hxF, hxy⟩,
		use [x, hxF],
		exact (func_class_spec φ_func x).2 hxy,
	},
	{
		rintro ⟨x, hxF, hxy⟩,
		unfold class_range_at has_mem.mem mem_class,

		use [x, hxF],
		rw← hxy,
		exact (func_class_spec φ_func x).1,
	},
end

lemma func_class_restriciton (φ : relation) [φ_func : class_function φ] 
(A : Set) : set_function (class_restriction φ A) :=
begin 
	fconstructor,
	intros x hx,
	unfold class_restriction at hx,
	rw mem_sep at hx,
	rcases hx with ⟨hxA, b, a, hx⟩,
	use [b, a, hx.1],

	intros c hc,
	unfold class_restriction at hc,
	rw mem_sep at hc,
	rcases hc with ⟨hcA, b', a', hc1, hc2⟩,
	rw ord_pair_eq_iff at hc1,
	rw [←hc1.1, ← hc1.2] at hc2,

	rcases φ_func.is_func a with ⟨y, hy1, hy2⟩,
	have hyc := hy2 hc2,
	have hyb := hy2 hx.2,
	rw [←hyc, ←hyb],
end


open_locale classical

def eval_full_set (f x : Set) : Set :=
if h : is_set_function f ∧ x ∈ domain f then 
@eval f x (set_func_of_is_set_func h.1) h.2
else ∅

infix ` @@ `:1000 := eval_full_set

lemma func_in {f x : Set} (hf : set_function f) (hx : x ∈ domain f) : 
f @@ x = @eval f x hf hx := dif_pos (and.intro hf.is_func hx)

lemma func_out {f x : Set} (h : ¬(is_set_function f ∧ x ∈ domain f)) : f @@ x = ∅ := 
dif_neg h

lemma domain_of_restriction (f A : Set) [set_function f] : 
domain (set_restriction f A) = domain f ∩ A :=
begin 
	ext x,
	split,
	{
		intro h,
		rw mem_pair_inter,
		rw mem_domain at *,
		cases h with b hb,
		rw mem_restriction at hb,
		rcases hb.2 with ⟨x', h', hb_2⟩,
		rw ord_pair_eq_iff at hb_2,
		cases hb_2 with hb_1 hb_2,
		rw← hb_2.1 at hb_1,
		use [b, hb.1, hb_1],
	},
	{
		intro h,
		rw mem_pair_inter at h,
		rw mem_domain at *,
		cases h.1 with b hb,
		use b,
		rw mem_restriction,
		use [hb, x, b, h.2],
	},
end

lemma domain_of_restriction_ss (f : Set) {A : Set} (hA : A ⊆ domain f) [set_function f] : 
domain (set_restriction f A) = A :=
begin 
	rw domain_of_restriction f A,
	rw eq_iff_subsets,
	use pair_inter_subset_right (domain f) A,

	intros a ha,
	rw mem_pair_inter,
	exact ⟨hA ha, ha⟩,
end

lemma func_ext {f g : Set} (f_func :set_function f) (
g_func :set_function g) (hfg : domain f = domain g) : f = g ↔ ∀⦃x⦄, 
x ∈ domain f → f @@ x = g @@ x :=
begin 
	split,
	{tauto,},
	{
		intro h,
		ext p,
		split,
		{
			intro hpf,
			rcases f_func.is_func hpf with ⟨b, a, hp⟩,
			rw hp.1 at hpf,
			have := h (mem_domain_pair hpf),
			rw func_in f_func (mem_domain_pair hpf) at this,
			rw← eval_unique f (mem_domain_pair hpf) hpf at this,
			have hag := (mem_domain_pair hpf),
			rw hfg at hag,
			rw func_in g_func hag at this,
			rw hp.1,
			rw this,
			cases eval_spec g hag with trash goal,
			exact goal,
		},
		{
			intro hpg,
			rw hfg at h,
			rcases g_func.is_func hpg with ⟨b, a, hp⟩,
			rw hp.1 at hpg,
			have := h (mem_domain_pair hpg),
			rw func_in g_func (mem_domain_pair hpg) at this,
			rw← eval_unique g (mem_domain_pair hpg) hpg at this,
			have hag := (mem_domain_pair hpg),
			rw← hfg at hag,
			rw func_in f_func hag at this,
			rw hp.1,
			rw← this,
			cases eval_spec f hag with trash goal,
			exact goal,
		},
	},
end

@[simp]lemma ord_not_le_iff (α β : Set) [ordinal α] [ordinal β] : ¬α ≤ β ↔ β < α :=
begin 
	split,
	{
		intro h,
		unfold has_lt.lt,
		exact ord_not_le h,
	},
	{
		intros h,
		unfold has_le.le,
		push_neg,
		by_contra h',
		push_neg at h',
		have := h' (not_ord_mem_ord _inst_2 h),
		rw this at h,
		exact not_ord_mem_ord _inst_2 h h,
	},
end

@[simp]lemma ord_not_lt_iff {α β : Set} [α_ord :ordinal α] [ordinal β] : ¬α < β ↔ β ≤ α :=
begin 
	rw ← ord_not_le_iff,
	simp,
end

lemma transfinite_induction (φ : fclass) (α : Set) [ordinal α] (hα : φ α) :
 ∃(γ : Set)[ordinal γ], φ γ ∧ ∀(ξ : Set) [ordinal ξ], φ ξ → γ ≤ ξ :=
begin 
	let X := {β ∈ α | φ β},
	by_cases hX : X = ∅,
	{
		use [α, _inst_1, hα],
		intros ξ ξ_ord hξ,
		by_contra,
		rw @ord_not_le_iff α ξ _inst_1 ξ_ord at h,
		have contra : ξ ∈ X,
		{
			rw mem_sep,
			unfold has_lt.lt at h,
			exact ⟨h, hξ⟩,
		},
		rw hX at contra,
		exact (mem_empty ξ).mp contra,
	},
	{
		have X_ord_class : subset_class X ON,
		{
			intros β hβ,
			rw mem_sep at hβ,
			exact mem_of_ordinal_is_ordinal (mem_ON_of_ord _inst_1) hβ.1,
		},

		rcases ON_ordinal_class.wo.wf X_ord_class hX with ⟨β, hβX, hβ⟩,
		have β_ord := ord_of_mem_ON (X_ord_class hβX),
		use [β, β_ord],
		rw mem_sep at hβX,
		use hβX.2,
		intros ξ ξ_ord hξ,
		by_contra,
		rw @ord_not_le_iff β ξ β_ord ξ_ord at h,
		unfold has_lt.lt at h,
		have hξα := _inst_1.tran hβX.1 h,
		have hξX : ξ ∈ X,
		{
			rw mem_sep,
			exact ⟨hξα, hξ⟩,
		},

		exact (hβ hξX) h,
	},
end

lemma restriction_agrees {f X : Set} (f_func : set_function f) {x : Set} (hxX : x ∈ X) :
f @@ x = set_restriction f X @@ x := 
begin 
	have rest_func := is_func_restriction f_func X,
	by_cases x ∈ domain f,
	{
		rw func_in f_func h,
		have hx_rest : x ∈ domain (set_restriction f X),
		{
			rw domain_of_restriction,
			rw mem_pair_inter,
			exact ⟨h, hxX⟩,
		},
		rw @func_in (set_restriction f X) x rest_func hx_rest,
		rw mem_domain at h,
		cases h with y hy,

		rw mem_domain at hx_rest,
		cases hx_rest with y' hy',
		rw mem_restriction at hy',

		have := func_out_unique hy hy'.1,

		rw ←eval_unique f h hy,
		rcases hy' with ⟨hyf', a, b, hab⟩,
		rw ord_pair_eq_iff at hab,
		cases hab with haX ha,
		rw ←ha.1 at haX,

		have pair_rest : ord_pair x y ∈ (set_restriction f X),
		{
			rw mem_restriction,
			use [hy, x, y, haX],
		},

		exact @eval_unique (set_restriction f X) x rest_func hx_rest y pair_rest,
	},
	{
		rw func_out (not_and_of_not_right (is_set_function f) h),
		have h2 : x ∉ domain (set_restriction f X),
		{
			intro h',
			rw domain_of_restriction at h',
			rw mem_pair_inter at h',
			exact h h'.1,
		},
		rw func_out (not_and_of_not_right (is_set_function (set_restriction f X)) h2),
	},
end

lemma nonempty_of_has_mem {x y: Set} (h : y ∈ x) : x ≠ ∅ :=
begin 
	intro hx,
	rw hx at h,
	simp at h,
	exact h,
end

lemma mem_range_of_mem_dom {f x : Set} (f_func : set_function f) (hx : x ∈ domain f) : f @@ x ∈ range f :=
begin 
	rw mem_range_iff_eval,
	use [x, hx],
	exact func_in f_func hx,
end

lemma func_spec {f x : Set} (f_func : set_function f)
 (hx : x ∈ domain f) : ord_pair x (f @@ x) ∈ f :=
begin 
	rw func_in f_func hx,
	cases eval_spec f hx,
	exact h,
end

lemma func_unique_iff {f x : Set} (f_func : set_function f) (hx : x ∈ domain f) (y : Set) : 
ord_pair x y ∈ f ↔ y = f @@ x :=
begin 
	split,
	{
		intro h,
		rw func_in f_func  hx,
		exact eval_unique f hx h,
	},
	{
		intro h,
		rw h,
		exact func_spec f_func hx,
	},
end

lemma func_unique {f x y : Set} (f_func :set_function f): 
ord_pair x y ∈ f → y = f @@ x :=
begin 
	intro h,
	have hx : x ∈ domain f,
	{
		rw mem_domain,
		use [y, h],
	},
	
	rwa func_unique_iff f_func hx y at h,
end

lemma mem_range_is_func {f y : Set} (f_func : set_function f) (hy : y ∈ range f) : 
∃x, x ∈ domain f ∧ f @@ x = y :=
begin 
	rw mem_range at hy,
	cases hy with x hx,
	use x,
	rw mem_domain,
	use [y, hx],
	exact eq.symm (func_unique f_func hx),
end

def identity (X : Set) : Set := {p ∈ X × X | ∃a, p = ord_pair a a}
lemma mem_identity (X : Set) : ∀x, x ∈ X ↔ ord_pair x x ∈ identity X :=
begin 
	intros x,
	unfold identity,
	rw mem_sep,
	rw mem_prod_pair,
	split,
	{
		intros hx,
		use [⟨hx, hx⟩, x],
	},
	{
		intro h,
		exact h.1.1,
	},
end

lemma mem_identity_pair (X a b : Set) : ord_pair a b ∈ identity X ↔
a ∈ X ∧ ord_pair a b = ord_pair a a :=
begin 
	split,
	{
		intro h,
		unfold identity at h,
		rw mem_sep at h,
		rcases h with ⟨habX, c, hc⟩,
		rw mem_prod_pair at habX,
		use habX.1,
		rw ord_pair_eq_iff at hc ⊢,
		use rfl,
		rw hc.1,
		exact hc.2,
	},
	{
		intros h,
		unfold identity,
		rw mem_sep,
		rw mem_prod_pair,
		rw ord_pair_eq_iff at h,
		simp at h,
		rw h.2,
		use [⟨h.1, h.1⟩],
		use a,
	},
end

lemma identity_func (X : Set) : set_function (identity X) :=
begin 
	fconstructor,
	intros p hp,
	unfold identity at hp,
	rw mem_sep at hp,
	rcases hp with ⟨hpXX, x, hpx⟩,
	rw hpx at hpXX,
	rw mem_prod_pair at hpXX,
	use [x, x, hpx],
	intros c hc,
	unfold identity at hc,
	rw mem_sep at hc,
	rcases hc with ⟨hcXX, a, ha⟩,
	rw ord_pair_eq_iff at ha,
	rw ha.1,
	rw ha.2,
end

lemma identity_domain (X : Set) : domain (identity X) = X :=
begin 
	ext p,
	split,
	{
		intro h,
		rw mem_domain at h,
		cases h with b hb,
		rw mem_identity_pair at hb,
		exact hb.1,
	},
	{
		intros hp,
		rw mem_domain,
		use p,
		rw mem_identity_pair,
		exact ⟨hp, rfl⟩,
	},
end

lemma identity_range (X : Set) : range (identity X) = X :=
begin 
	ext p,
	split,
	{
		intro h,
		rw mem_range at h,
		cases h with a ha,
		rw mem_identity_pair at ha,
		rw ord_pair_eq_iff at ha,
		rw ha.2.2,
		exact ha.1,
	},
	{
		intro h,
		rw mem_range,
		use p,
		rw mem_identity_pair,
		exact ⟨h, rfl⟩,
	},
end

lemma identity_injective (X : Set) : injective (identity X) :=
begin 
	intros x x' y hxy hx'y,
	rw mem_identity_pair at *,
	rw ord_pair_eq_iff at *,
	simp at *,
	rw← hxy.2,
	exact hx'y.2,
end

lemma eval_identity {X x : Set} (hx : x ∈ X) : (identity X) @@ x = x :=
begin 
	rw← identity_domain X at hx,
	have := @func_spec (identity X) x (identity_func X) hx,
	rw mem_identity_pair at this,
	rw ord_pair_eq_iff at this,
	exact this.2.2,
end

structure ordered_set :=
(set : Set)
(r : relation)

instance : has_mem Set ordered_set := ⟨λx y, x ∈ y.set⟩

structure order_isomorphism (f A : Set) (rA : relation) (B : Set) (rB : relation)
extends bijection f A B :=
(f_isomorphism : ∀⦃a1 a2⦄, a1 ∈ A → a2 ∈ A → (rA a1 a2 ↔ rB (f @@ a1) (f @@ a2)))

def gen_relation (α β : Type*) := α → β → Prop

def gen_relation_refl {α : Type*} (r : gen_relation α α) : Prop :=
∀x : α, r x x

def gen_relation_symm {α : Type*} (r : gen_relation α α) : Prop :=
∀⦃x y : α⦄, r x y → r y x

def gen_relation_tran {α : Type*} (r : gen_relation α α) : Prop :=
∀⦃x y z : α⦄, r x y → r y z → r x z

structure gen_equiv_relation {α : Type*} (r : gen_relation α α) := 
(refl : gen_relation_refl r)
(symm : gen_relation_symm r)
(tran : gen_relation_tran r)

def order_isomorphic : gen_relation ordered_set ordered_set  :=
λ A B, ∃f (f_iso : order_isomorphism f A.set A.r B.set B.r), true

theorem ord_isomorphism_is_trivial {α β : Set} (_inst_1 : ordinal α) 
(_inst_2 : ordinal β) {f : Set} (f_iso : order_isomorphism f α (∈) β (∈)) :
 f = identity α :=
begin
	have : domain f = domain (identity α),
	{
		rw identity_domain,
		rwa f_iso.f_domain,
	},
	rw func_ext f_iso.f_func (identity_func α) this,
	rw f_iso.f_domain,
	clear this,

	have hfξ : ∀ξ∈ α, f @@ ξ = {δ ∈ β | ∃γ, f @@ γ = δ ∧ γ ∈ ξ},
	{
		intros ξ hξα,
		ext δ,
		split,
		{
			intro h,
			rw mem_sep,
			rw← f_iso.f_domain at hξα,

			have hfξ := mem_range_of_mem_dom f_iso.f_func hξα,
			rw f_iso.f_range at hfξ,
			have hδβ := (_inst_2.tran hfξ) h,
			use hδβ,
			rw← f_iso.f_range at hδβ,
			rw mem_range at hδβ,
			cases hδβ with γ hγ,
			use γ,
			have hγ_dom : γ ∈ domain f,
			{
				rw mem_domain,
				use [δ, hγ],
			},
			have hγδ := eq.symm (func_unique f_iso.f_func hγ),
			use hγδ,
			by_contra hcontra,
			rw f_iso.f_domain at hξα,
			have ξ_ord : ξ ∈ ON,
			{
				exact mem_of_ordinal_is_ordinal (mem_ON_of_ord _inst_1) hξα,
			},
			rw f_iso.f_domain at hγ_dom,
			have γ_ord : γ ∈ ON := mem_of_ordinal_is_ordinal (mem_ON_of_ord _inst_1) hγ_dom,
			have fξ_ord : f @@ ξ ∈ ON := mem_of_ordinal_is_ordinal (mem_ON_of_ord _inst_2) hfξ,

			cases ON_ordinal_class.wo.tri ξ_ord γ_ord,
			{
				rw f_iso.f_isomorphism hξα hγ_dom at h_1,
				rw hγδ at h_1,
				exact not_ord_mem_ord (ord_of_mem_ON fξ_ord) h_1 h,
			},
			{
				cases h_1,
				{exact hcontra h_1},
				{
					have : f @@ ξ = f @@ γ := congr_arg (eval_full_set f) h_1,
					rw← this at hγδ,
					rw← hγδ at h,
					exact ord_not_mem_self fξ_ord h,
				},
			},
		},
		{
			intro h,
			rw mem_sep at h,
			rcases h with ⟨hδβ, γ, hγ⟩,
			rw← hγ.1,

			have hγα : γ ∈ α := _inst_1.tran hξα hγ.2,

			rw← f_iso.f_isomorphism hγα hξα,
			exact hγ.2,
		},
	},
	
	let X := {ξ ∈ α | f @@ ξ ≠ ξ},
	by_cases X_empty : X = ∅,
	{
		intros ξ hξα,
		rw eval_identity hξα,
		by_contra,
		have hξX : ξ ∈ X,
		{
			rw mem_sep,
			exact ⟨hξα, h⟩,
		},
		rw X_empty at hξX,
		simp at hξX,
		exact hξX,
	},
	{
		have X_ss : X ⊆ α,
		{
			intros x hx,
			rw mem_sep at hx,
			exact hx.1,
		},
		exfalso,
		rcases _inst_1.wo.wf X_ss X_empty with ⟨ξ, hξX, ξ_min⟩,
		rw mem_sep at hξX,
		have contra : f @@ ξ = ξ,
		{
			rw hfξ ξ hξX.1,
			have ξ_ord : ordinal ξ := ord_of_mem_ON 
			(mem_of_ordinal_is_ordinal (mem_ON_of_ord _inst_1) hξX.1),

			have temp : ∀⦃γ⦄, γ ∈ ξ → f @@ γ = γ,
			{
				intros γ hγ,
				by_contra,
				have : γ ∈ X,
				{
					rw mem_sep,
					use _inst_1.tran hξX.1 hγ,
				},
				exact ξ_min this hγ,
			},

			ext δ,
			split,
			{
				rw mem_sep,
				intro h,
				rcases h with ⟨hδβ, γ, hγ⟩,
				have := temp hγ.2,
				rw← hγ.1,
				rw this,
				exact hγ.2,
			},
			{
				intro h,
				rw mem_sep,
				have hfδ := temp h,
				have hδ_dom : δ ∈ domain f,
				{
					rw f_iso.f_domain,
					exact _inst_1.tran hξX.1 h,
				},
				have hδβ := mem_range_of_mem_dom f_iso.f_func hδ_dom,
				rw f_iso.f_range at hδβ,
				rw hfδ at hδβ,
				use [hδβ, δ, hfδ, h],
			},
		},

		exact hξX.2 contra,
	},
end

lemma ord_isomorphism_self (X : Set) (rX : relation) : 
order_isomorphism (identity X) X rX X rX :=
{

	f_func := identity_func X,
	f_domain := identity_domain X,
	f_range := identity_range X,
	f_injective := identity_injective X,
	f_isomorphism := 
	begin 
		intros x1 x2 hx1 hx2,
		rw [eval_identity hx1, eval_identity hx2],
	end
}

lemma ordinals_isomorphic_iff_eq {α β : Set} (_inst_1 : ordinal α) 
(_inst_2 : ordinal β) :(∃(f : Set) 
[f_iso : order_isomorphism f α (∈) β (∈)], true) ↔ α = β :=
begin 
	split,
	{
		intro h,
		rcases h with ⟨f, f_iso, _⟩, clear h_h_h,
		have f_id := ord_isomorphism_is_trivial _inst_1 _inst_2 f_iso,
		ext γ,
		split,
		{
			intros hγ,
			have hγ_dom : γ ∈ domain f := by rwa← f_iso.f_domain at hγ,
			have : f @@ γ ∈ range f := mem_range_of_mem_dom f_iso.f_func hγ_dom,
			rwa [f_iso.f_range, f_id, eval_identity hγ] at this,
		},
		{
			intro hγ,
			have hγ_ran : γ ∈ range f := by rwa← f_iso.f_range at hγ,
			rw f_id at hγ_ran,
			rcases mem_range_is_func (identity_func α) hγ_ran with ⟨x, hx_dom, hx⟩,
			have hxα : x ∈ α := by rwa (identity_domain) at hx_dom,
			rw eval_identity hxα at hx,
			rwa← hx,
		},
	},
	{
		intros h,
		have id_iso := ord_isomorphism_self α (∈),
		rw← h,
		use [identity α, id_iso],
	},
end

def dict_order (rX rY : relation) : relation :=
 λp1 p2 , ∃a b a' b', (p1 = ord_pair a b ∧ p2 = ord_pair a' b' ∧
 (rX a a' ∨ (a = a' ∧ rY b b')))

lemma dict_pair (rX rY : relation) (a b a' b' : Set) :
(dict_order rX rY) (ord_pair a b) (ord_pair a' b') ↔ (rX a a' ∨ (a = a' ∧ rY b b'))
:= 
begin 
	unfold dict_order,
	split,
	{
		intro h,
		rcases h with ⟨a_1, b_1, a_1', b_1', hab_1⟩,
		rw ord_pair_eq_iff at hab_1,
		rcases hab_1 with ⟨hab_1, habab', hab_1ab'⟩,
		rw← hab_1.1 at hab_1ab',
		rw← hab_1.2 at hab_1ab',
		rw ord_pair_eq_iff at habab',
		rw← habab'.1 at hab_1ab',
		rw← habab'.2 at hab_1ab',
		exact hab_1ab',
	},
	{
		intro h,
		use [a, b, a', b', rfl, rfl, h],
	},
end

lemma dict_wo {X Y : Set} {rX rY : relation} (X_wo : well_order X rX) (Y_wo : well_order Y rY) :
well_order (X × Y) (dict_order rX rY) :=
begin 
	fconstructor,
	{
		intros p hp h,
		rw mem_prod at hp,
		rcases hp with ⟨a, b, haX, hbY, hp⟩,
		rw hp at h,
		rw dict_pair at h,
		simp at h,
		cases h,
		{exact (X_wo.irrfl haX) h},
		{exact (Y_wo.irrfl hbY) h},
	},
	{
		intros p q r hp hq hr hpq hqr,
		rw mem_prod at hp hq hr,

		rcases hp with ⟨a, b, haX, hbY, hp⟩,
		rcases hq with ⟨c, d, hcX, hdY, hq⟩,
		rcases hr with ⟨e, f, heX, hfY, hr⟩,

		rw hp at hpq ⊢,
		rw hq at hpq hqr,
		rw hr at hqr ⊢,
		rw dict_pair at hpq hqr ⊢,
		cases hpq,
		{
			cases hqr,
			{
				left,
				exact X_wo.tran haX hcX heX hpq hqr,
			},
			{

				rw← hqr.1,
				left,
				exact hpq,
			},
		},
		{
			cases hqr,
			{
				rw← hpq.1 at hqr,
				left,
				exact hqr,
			},
			{
				right,
				rw hpq.1,
				use hqr.1,
				exact Y_wo.tran hbY hdY hfY hpq.2 hqr.2,
			},
		},
	},
	{
		intros p q hp hq,
		rw mem_prod at hp hq,
		rcases hp with ⟨a, b, haX, hbY, hp⟩,
		rcases hq with ⟨c, d, hcX, hdY, hq⟩,
		rw [hp, hq],
		have tri_ac := X_wo.tri haX hcX,
		have tri_bd := Y_wo.tri hbY hdY,
		cases tri_ac,
		{
			left,
			rw dict_pair,
			left,
			exact tri_ac,
		},
		{
			cases tri_ac,
			{
				right, left,
				rw dict_pair,
				left,
				exact tri_ac,
			},
			{
				cases tri_bd,
				{
					left,
					rw dict_pair,
					right,
					exact ⟨tri_ac, tri_bd⟩,
				},
				{
					cases tri_bd,
					{
						right,left,
						rw dict_pair,
						right,
						exact ⟨eq.symm tri_ac, tri_bd⟩,
					},
					{
						right, right,
						rw ord_pair_eq_iff,
						exact ⟨tri_ac, tri_bd⟩,
					},
				},
			},
		},
	},
	{
		intros K K_ss K_nonempty,
		cases nonempty_has_mem K_nonempty with p hpK,
		have hXY := K_ss hpK,
		rw mem_prod at hXY,
		rcases hXY with ⟨a, b, haX, hbY, hp⟩,

		have domK_nonempty : domain K ≠ ∅,
		{
			have : a ∈ domain K,
			{
				rw mem_domain,
				use b,
				rw← hp,
				exact hpK,
			},
			exact nonempty_of_has_mem this,
		},
		have rangeK_nonempty : range K ≠ ∅,
		{
			have : b ∈ range K,
			{
				rw mem_range,
				use a,
				rw← hp,
				exact hpK,
			},
			exact nonempty_of_has_mem this,
		},

		have domK_ss : domain K ⊆ X,
		{
			intros x hx,
			rw mem_domain at hx,
			rcases hx with ⟨y, hxy⟩,
			have := K_ss hxy,
			rw mem_prod_pair at this,
			exact this.1,
		},

		have rangeK_ss : range K ⊆ Y,
		{
			intros y hy,
			rw mem_range at hy,
			rcases hy with ⟨x, hxy⟩,
			have := K_ss hxy,
			rw mem_prod_pair at this,
			exact this.2,
		},

		rcases X_wo.wf domK_ss domK_nonempty with ⟨x, hxK, x_min⟩,
		let S := {y ∈ Y | ord_pair x y ∈ K},
		have S_ss : S ⊆ Y,
		{
			intros y hy,
			rw mem_sep at hy,
			exact hy.1,
		},
		have S_nonempty : S ≠ ∅,
		{
			rw mem_domain at hxK,
			rcases hxK with ⟨y, hy⟩,
			have : y ∈ S,
			{
				rw mem_sep,
				have := K_ss hy,
				rw mem_prod_pair at this,
				exact ⟨this.2, hy⟩,
			},
			exact nonempty_of_has_mem this,
		},

		rcases Y_wo.wf S_ss S_nonempty with ⟨y, hyS, y_min⟩,
		have hxyK : ord_pair x y ∈ K,
		{
			rw mem_sep at hyS,
			exact hyS.2,
		},
		use [ord_pair x y, hxyK],
		intros p hp hcontra,
		have hpXY := K_ss hp,
		rw mem_prod at hpXY,
		rcases hpXY with ⟨a, b, haX, hbY, hp⟩,
		rw hp at hcontra,
		rw dict_pair at hcontra,

		have haK : a ∈ domain K,
		{
			rw mem_domain,
			use b,
			rwa← hp,
		},

		cases hcontra,
		{
			exact (x_min haK) hcontra,
		},
		{
			have hbS : b ∈ S,
			{
				rw mem_sep,
				use hbY,
				rw← hcontra.1,
				rwa← hp,
			},
			exact (y_min hbS) hcontra.2,
		},
	},
end

lemma inverse_of_inverse {f : Set} (f_func : set_function f) : f = inv (inv f) :=
begin 
	ext p,
	split,
	{
		intro hpf,
		rw mem_inv,
		rcases f_func.is_func hpf with ⟨b, a, hp⟩,
		use [ord_pair b a, b, a],
		rw mem_inv,
		use [p, a, b, hpf, hp.1, rfl, rfl, hp.1],
	},
	{
		intro hpiif,
		rw mem_inv at hpiif,
		rcases hpiif with ⟨n, b, a, hnif, hn, hp⟩,
		rw mem_inv at hnif,
		rcases hnif with ⟨p', a', b', hp'f, hp', hn2⟩,
		rw hn2 at hn,
		rw ord_pair_eq_iff at hn,
		rw hn.1 at hp',
		rw hn.2 at hp',
		rw← hp' at hp,
		rwa← hp at hp'f,
	},
end

lemma inv_range {f : Set} (f_func : set_function f) : range (inv f) = domain f :=
congr_arg domain (eq.symm (inverse_of_inverse f_func))

lemma inv_domain (f : Set) : domain (inv f) = range f := rfl

lemma mem_inv_pair (f : Set) (a b : Set) : ord_pair a b ∈ inv f ↔ ord_pair b a ∈ f :=
begin 
	rw mem_inv,
	split,
	{
		intro h,
		rcases h with ⟨p, b', a', hpf, hp, hab'⟩,
		rw ord_pair_eq_iff at hab',
		rw← hab'.1 at hp,
		rw← hab'.2 at hp,
		rwa ←hp,
	},
	{
		intro h,
		use [ord_pair b a, b, a, h, rfl],
	},
end

lemma func_inv {f : Set} (f_func : set_function f) (f_inj : injective f) {y : Set}
(hy : y ∈ domain (inv f)) : f @@ (inv f @@ y) = y :=
begin 
	have := @func_spec (inv f) y (inv_of_inj_is_func f_func f_inj) hy,
	rw mem_inv_pair at this,
	exact eq.symm (func_unique f_func this),
end

lemma injective_iff {f : Set} (f_func : set_function f) : injective f ↔ ∀⦃x y⦄ 
(hxf : x ∈ domain f) (hyf : y ∈ domain f), f @@ x = f @@ y →
x = y :=
begin 
	rw injective_iff_bad,
	split,
	{
		intros h x x' hx hx' hxx',
		rw func_in f_func hx at hxx',
		rw func_in f_func hx' at hxx',
		exact h hxx',
	},
	{
		intros h x x' hx hx' hxx',
		rw← func_in f_func hx at hxx',
		rw← func_in f_func hx' at hxx',
		exact h hx hx' hxx',
	},
end

lemma inv_inj {f : Set} (f_func : set_function f) (f_inj : injective f) :
injective (inv f) :=
begin
	rw injective_iff (inv_of_inj_is_func f_func f_inj),
	intros y y' hy hy' hyy',
	rw [ ←func_inv f_func f_inj hy, ←func_inv f_func f_inj hy', hyy'],
end

lemma inv_func {f : Set} (f_func : set_function f) (f_inj : injective f) {x : Set}
(hx : x ∈ domain f) : (inv f) @@ (f @@ x) = x :=
begin 
	have := inverse_of_inverse f_func,
	have obv : inv f @@ (f @@ x) = inv f @@ (inv (inv f) @@ x) := 
	congr rfl (congr_fun (congr_arg eval_full_set this) x),
	rw obv, clear obv,
	rw this at hx,
	have := func_inv (inv_of_inj_is_func f_func f_inj) _ hx,
	exact this,

	exact inv_inj f_func f_inj,
end

lemma inverse_order_isomorphism {f A B : Set} {rA rB : relation} 
(iso : order_isomorphism f A rA B rB) : order_isomorphism (inv f) B rB A rA :=
{
	f_func := @inv_of_inj_is_func f iso.f_func iso.f_injective,
	f_domain := begin 
		rw← iso.f_range,
		unfold range,
	end,
	f_range := begin 
		unfold range,
		rw← iso.f_domain,
		have := @inverse_of_inverse f iso.f_func,
		exact congr_arg domain (eq.symm this),
	end,
	f_injective := 
	begin 
		intros x1 x2 y hx1y hx2y,
		rw mem_inv_pair at hx1y hx2y,
		exact @func_out_unique f iso.f_func y x1 x2 hx1y hx2y,
	end,
	f_isomorphism := begin 
		intros b1 b2 hb1 hb2,
		have inv_func := @inv_of_inj_is_func f iso.f_func iso.f_injective,
		have hbA : ∀⦃b1⦄, b1 ∈ B → (inv f) @@ b1 ∈ A,
		{
			intros b1 hb1,
			rw← iso.f_domain,
			have dom_inv : domain (inv f) = range f := by unfold range,
			rw iso.f_range at dom_inv,
			rw← dom_inv at hb1 hb2,
			rw← @inv_range f iso.f_func,
			rw mem_range,
			use b1,
			rw mem_inv_pair,
			have := @func_inv f iso.f_func iso.f_injective b1 hb1,
			rw func_unique_iff iso.f_func,
			exact eq.symm this,
			rw mem_domain,
			use b1,
			have obv : ord_pair (inv f @@ b1) b1 = ord_pair (inv f @@ b1) (f @@ (inv f @@ b1)) :=
			congr_arg (ord_pair (inv f @@ b1)) (eq.symm this),
			rw obv,

			have h_dom : (inv f) @@ b1 ∈ domain f,
			{
				have := mem_range_of_mem_dom inv_func hb1,
				rwa @inv_range f iso.f_func at this,
			},
			exact @func_spec f ((inv f) @@ b1) iso.f_func h_dom,
		},

		have hb1A := hbA hb1,
		have hb2A := hbA hb2,
		have hb1_dom : b1 ∈ domain (inv f),
		{
			have : domain (inv f) = range f := by unfold range,
			rw this,
			rwa iso.f_range,
		},
		have hb2_dom : b2 ∈ domain (inv f),
		{
			have : domain (inv f) = range f := by unfold range,
			rw this,
			rwa iso.f_range,
		},
		have hb1_inv := func_inv iso.f_func iso.f_injective hb1_dom,
		have hb2_inv := func_inv iso.f_func iso.f_injective hb2_dom,
		split,
		{
			intro h,
			rw [←hb1_inv, ←hb2_inv] at h,
			rwa iso.f_isomorphism hb1A hb2A,
		},
		{
			intro h,
			rw iso.f_isomorphism hb1A hb2A at h,
			rwa [hb1_inv, hb2_inv] at h,
		},
	end
}

lemma domain_comp {g f : Set} (g_func : set_function g) (f_func : set_function f) : 
domain (g ∘ f) = { x ∈ domain f | f @@ x ∈ domain g} := 
begin 
	rw domain_of_comp_bad,
	ext x,
	rw [mem_sep, mem_sep],
	split,
	{
		intro h,
		rcases h with ⟨hxf1, hxf2, hx_eval⟩,
		use hxf1,
		rwa func_in f_func hxf2,
	},
	{
		intro h,
		use [h.1, h.1],
		rw← func_in f_func h.1,
		exact h.2,
	},
end

lemma eval_comp {g f x : Set} (g_func : set_function g) (f_func : set_function f)
 (hx : x ∈ domain (g ∘ f)) : (g ∘ f) @@ x = g @@ (f @@ x) :=
begin
	have hx2 : x ∈ domain f ∧ f @@ x ∈ domain g,
	{
		rwa [domain_comp, mem_sep] at hx;
		assumption,
	},

	have h := @func_spec (g ∘ f) x (comp_is_func g_func f_func) hx,

	rw mem_comp_pair at h,
	rcases h with ⟨y, hxyf, hy⟩,
	rw func_unique f_func hxyf at hy,
	exact func_unique g_func hy,
end

lemma domain_comp' {g f : Set} (g_func : set_function g)
(f_func : set_function f) (hfg : range f = domain g) : 
domain (g ∘ f) = domain f :=
begin 
	rw domain_comp g_func f_func,
	ext x,
	rw mem_sep,
	split,
	{
		intro h, exact h.1,
	},
	{
		intro h, use h,
		rw← hfg,
		exact mem_range_of_mem_dom f_func h,
	},
end

lemma mem_range_iff {f : Set} (f_func :set_function f) : ∀⦃y⦄, y ∈ range f ↔
 ∃(x : Set) (hx : x ∈ domain f), y = f @@ x :=
 begin 
	 intros y,
	 rw mem_range_iff_eval,
	 split,
	 {
		 intro h,
		 rcases h with ⟨x, hx, hxy⟩,
		 use [x, hx],
		 rw hxy,
		 exact eq.symm (func_in f_func hx),
	 },
	 {
		intro h,
		rcases h with ⟨x, hx, hxy⟩,
		use [x, hx],
		rw hxy,
		exact (func_in f_func hx),
	 }
 end

lemma range_comp' {g f : Set} (g_func : set_function g)
(f_func : set_function f) (hfg : range f = domain g) :
 range (g ∘ f) = range g :=
begin 
	ext z,
	rw mem_range_iff (comp_is_func g_func f_func),
	split,
	{
		intro h,
		rcases h with ⟨x, hx, hxz⟩,
		rw hxz,
		rw eval_comp g_func f_func hx,
		rw domain_comp' g_func f_func hfg at hx,
		have := mem_range_of_mem_dom f_func hx,
		rw hfg at this,
		exact mem_range_of_mem_dom g_func this,
	},
	{
		intro h,
		rw mem_range_iff g_func at h,
		rcases h with ⟨y, hy, hyz⟩,
		rw← hfg at hy,
		rw mem_range_iff f_func at hy,
		rcases hy with ⟨x, hx, hxy⟩,
		rw domain_comp' g_func f_func hfg,
		use [x, hx],
		rw [hyz, hxy],
		rw← domain_comp' g_func f_func hfg at hx,
		exact eq.symm (eval_comp g_func f_func hx),
	},
end

lemma comp_inj {g f : Set} (g_func : set_function g)
(f_func : set_function f) (g_inj : injective g) (f_inj : injective f) 
(hfg : range f = domain g) : injective (g ∘ f) :=
begin 
	rw injective_iff (comp_is_func g_func f_func),
	rw injective_iff g_func at g_inj,
	rw injective_iff f_func at f_inj,

	intros x y hx hy hxy,
	rw [eval_comp g_func f_func hx, eval_comp g_func f_func hy] at hxy,
	rw domain_comp' g_func f_func hfg at hx hy,
	have := @g_inj (f @@ x) (f @@ y) _ _ hxy,
	{
		exact f_inj hx hy this,
	},
	{
		rw← hfg,
		exact mem_range_of_mem_dom f_func hx,
	},
	{
		rw← hfg,
		exact mem_range_of_mem_dom f_func hy,
	},
end

lemma order_isomorphism_comp {f g A B C : Set} {rA rB rC : relation} 
(f_iso : order_isomorphism f A rA B rB) (g_iso : order_isomorphism g B rB C rC)
: order_isomorphism (g ∘ f) A rA C rC := {
	f_func := @comp_is_func g f g_iso.f_func f_iso.f_func,
	f_domain := 
	begin
		rw domain_comp' g_iso.f_func f_iso.f_func,
		{exact f_iso.f_domain},
		{rw [f_iso.f_range, g_iso.f_domain]},
	end,
	f_range :=
	begin 
		rw range_comp' g_iso.f_func f_iso.f_func,
		{exact g_iso.f_range},
		{rw [f_iso.f_range, g_iso.f_domain]},
	end,
	f_injective := 
	begin
		apply comp_inj g_iso.f_func f_iso.f_func g_iso.f_injective f_iso.f_injective,
		rw [f_iso.f_range, g_iso.f_domain],
	end,
	f_isomorphism :=
	begin 
		 intros a1 a2 ha1 ha2,
		 have hfg : range f = domain g := by rw [f_iso.f_range, g_iso.f_domain],

		 rw[←f_iso.f_domain, ←domain_comp' g_iso.f_func f_iso.f_func hfg] at ha1 ha2,
		 rw [eval_comp g_iso.f_func f_iso.f_func ha1, 
		 eval_comp g_iso.f_func f_iso.f_func ha2],
		 
		 rw domain_comp' g_iso.f_func f_iso.f_func hfg at ha1 ha2,
		 have hfB : f @@ a1 ∈ B ∧ f @@ a2 ∈ B,
		 {
			 rw← f_iso.f_range,
			 exact ⟨mem_range_of_mem_dom f_iso.f_func ha1, mem_range_of_mem_dom f_iso.f_func ha2⟩,
		 },
		 rw← g_iso.f_isomorphism hfB.1 hfB.2,
		 rw f_iso.f_domain at ha1 ha2,

		 exact f_iso.f_isomorphism ha1 ha2,
	end
}


lemma order_isomorphism_equiv : gen_equiv_relation order_isomorphic :=
begin 
	fconstructor,
	{
		intros X,
		use [identity X.set, ord_isomorphism_self X.set X.r],
	},
	{
		intros X Y XY_iso,
		rcases XY_iso with ⟨f, f_iso, -⟩,
		use [inv f, inverse_order_isomorphism f_iso],
	},
	{
		intros X Y Z hXY hYZ,
		rcases hXY with ⟨f, f_iso, -⟩,
		rcases hYZ with ⟨g, g_iso, -⟩,
		use g ∘ f,
		use order_isomorphism_comp f_iso g_iso,
	},
end

lemma order_isomorphism_preserves_minimal (f A B : Set) (rA rB : relation) 
(f_iso : order_isomorphism f A rA B rB) {a : Set} {haA : a ∈ A} 
(ha : minimal rA haA) : ∃hfa : f @@ a ∈ B, minimal rB hfa :=
begin 
	rw← f_iso.f_range,
	have ha_dom : a ∈ domain f := by rwa← f_iso.f_domain at haA,
	use mem_range_of_mem_dom f_iso.f_func ha_dom,
	unfold minimal,

	by_contra hcontra,

	push_neg at hcontra,
	rcases hcontra with ⟨y, hy_ran, hyfa⟩,
	cases mem_range_is_func f_iso.f_func hy_ran with x hx,
	rw← hx.2 at hyfa,

	have hxA : x ∈ A ,
	{
		rw f_iso.f_domain at hx,
		exact hx.1,
	},

	rw← f_iso.f_isomorphism hxA haA at hyfa,
	exact ha hxA hyfa,
end

postfix ⁻¹ := inv

lemma func_comp_inv_is_identity {f : Set} (f_func : set_function f) 
(f_inj : injective f) : f ∘ f⁻¹ = identity (range f) :=
begin 
	have f_inv_func := inv_of_inj_is_func f_func f_inj,
	have comp_dom := domain_comp f_func f_inv_func,
	rw inv_domain at comp_dom,
	have h_dom : domain (f ∘ f⁻¹) = domain (identity (range f)),
	{
		rw identity_domain,
		rw comp_dom,
		ext x,
		rw mem_sep,
		split,
		{
			intro h, exact h.1,
		},
		{
			intro h,
			use h,
			rw← inv_domain at h,
			rw← inv_range f_func,
			exact mem_range_of_mem_dom f_inv_func h,
		},
	},

	have comp_func := @comp_is_func f f⁻¹ f_func f_inv_func,
	rw func_ext comp_func (identity_func (range f)) h_dom,
	intros x hx_comp,
	have hx_id : x ∈ range f,
	{
		rw h_dom at hx_comp,
		rwa identity_domain (range f) at hx_comp,
	},
	rw eval_identity hx_id,
	rw eval_comp f_func f_inv_func hx_comp,
	exact func_inv f_func f_inj hx_id,
end

lemma inv_comp_func_is_identity {f : Set} (f_func : set_function f) 
(f_inj : injective f) : f⁻¹ ∘ f = identity (domain f) :=
begin 
	have obv : f⁻¹ ∘ f = f⁻¹ ∘ f⁻¹⁻¹ := congr_arg (comp f⁻¹) 
	(inverse_of_inverse f_func),
	rw obv,
	rw func_comp_inv_is_identity (inv_of_inj_is_func f_func f_inj)
	(inv_inj f_func f_inj),
	rw inv_range f_func,
end

lemma comp_identity {f : Set} (f_func : set_function f) : 
f ∘ (identity (domain f)) = f :=
begin
	 have id_func := identity_func (domain f),
	 have h_dom : domain (f∘identity (domain f)) = domain f,
	 	{
		 rw domain_comp f_func id_func,
		 ext x,
		 rw mem_sep,
		 rw identity_domain,
		 split,
		 {
			 intro h, exact h.1,
		 },
		 {
			 intro h, use h,
			 rwa eval_identity h,
		 },
	 },
	 
	 rw func_ext,
	 {
		 intros x hx1,
		 rw eval_comp f_func id_func hx1,
		 rw h_dom at hx1,
		 rw eval_identity hx1,
	 },
	 {exact comp_is_func f_func id_func},
	 {exact f_func},
	 {exact h_dom},
end

lemma identity_comp {f : Set} (f_func : set_function f) : 
(identity (range f)) ∘ f = f :=
begin 
	 have id_func := identity_func (range f),
	 have h_dom : domain (identity (range f) ∘ f) = domain f,
	 {
			rw domain_comp id_func f_func,
			rw identity_domain,
			ext x,
			rw mem_sep,
			split,
			{
				intro h, exact h.1,
			},
			{
				intro h, use h,
				exact mem_range_of_mem_dom f_func h,
			},
	 },

	rw func_ext (comp_is_func id_func f_func) f_func h_dom,
	intros x hx,
	rw eval_comp id_func f_func hx,
	rw h_dom at hx,
	rw eval_identity (mem_range_of_mem_dom f_func hx),
end

lemma comp_assoc {f g h : Set} (f_func : set_function f) (g_func : set_function g)
(h_func : set_function h) (h_hg : range h ⊆ domain g) (h_gf : range g ⊆ domain f) 
: f ∘ (g ∘ h) = (f ∘ g) ∘ h :=
begin
	have gh_func := comp_is_func g_func h_func,
	have fg_func := comp_is_func f_func g_func,
	have f_gh_func := comp_is_func f_func gh_func,
	have fg_h_func := comp_is_func fg_func h_func,
	have h_dom : domain (f∘(g∘h)) = domain (f∘g∘h),
		{
		rw domain_comp f_func gh_func,
		rw domain_comp fg_func h_func,
		ext x,
		rw [mem_sep],
		split,
		{
			intros hx,
			have hx_gh := hx.1,
			rw [mem_sep, domain_comp f_func g_func, mem_sep],
			rw [domain_comp g_func h_func, mem_sep] at hx,
			use hx.1.1,
			use h_hg (mem_range_of_mem_dom h_func hx.1.1),
			rw eval_comp  g_func h_func hx_gh at hx,
			exact hx.2,
		},
		{
			intro hx,
			rw mem_sep at hx,
			rw [domain_comp g_func h_func, mem_sep],
			split,
			{
				use hx.1,
				exact h_hg (mem_range_of_mem_dom h_func hx.1),
			},
			{
				apply h_gf,
				have : x ∈ domain (g ∘ h),
				{
					rw [domain_comp g_func h_func, mem_sep],
					use hx.1,
					exact h_hg (mem_range_of_mem_dom h_func hx.1),
				},
				rw eval_comp g_func h_func this,
				exact mem_range_of_mem_dom g_func (h_hg (mem_range_of_mem_dom h_func hx.1)),
			},
		},
	},

	rw func_ext f_gh_func fg_h_func h_dom, swap,
	
	intros x hx,
	rw eval_comp f_func gh_func hx,
	rw h_dom at hx,
	rw eval_comp fg_func h_func hx,
	have hxh : x ∈ domain h,
	{
		rw domain_comp fg_func h_func at hx,
		rw mem_sep at hx, exact hx.1,
	},
	have hx_gh : x ∈ domain (g ∘ h),
	{
		rw [domain_comp g_func h_func, mem_sep], use hxh,
		exact h_hg (mem_range_of_mem_dom h_func hxh),
	},
	have : h @@ x ∈ domain (f ∘ g),
	{
		rw [domain_comp f_func g_func, mem_sep],
		have := h_hg (mem_range_of_mem_dom h_func hxh),
		use this,
		exact h_gf (mem_range_of_mem_dom g_func this),
	},

	rw eval_comp g_func h_func hx_gh,
	rw eval_comp f_func g_func this,
end

lemma comp_assoc' {f g h : Set} (f_func : set_function f) (g_func : set_function g)
(h_func : set_function h) (h_hg : range h = domain g) (h_gf : range g = domain f) 
: f ∘ (g ∘ h) = (f ∘ g) ∘ h :=
begin 
	rw eq_iff_subsets (range h) (domain g) at h_hg,
	rw eq_iff_subsets (range g) (domain f) at h_gf,
	exact comp_assoc f_func g_func h_func h_hg.1 h_gf.1,
end

lemma order_isomorphism_unique {A : Set} {R : relation} {α : Set} 
(α_ord : ordinal α) {f g : Set}
(f_iso : order_isomorphism f A R α (∈))
(g_iso : order_isomorphism g A R α (∈)) : f = g :=
begin 
	have invg_iso := inverse_order_isomorphism g_iso,
	have fg_iso := order_isomorphism_comp invg_iso f_iso,

	have hfg := ord_isomorphism_is_trivial α_ord α_ord fg_iso,
	have : (f ∘ g⁻¹) ∘ g = (identity α) ∘ g := congr_fun (congr_arg comp hfg) g,
  have temp : range g⁻¹ = domain f,
	{
		rw inv_range g_iso.f_func,
		rw g_iso.f_domain,
		rw f_iso.f_domain,
	},
	have temp2 := comp_assoc' f_iso.f_func invg_iso.f_func g_iso.f_func rfl temp,
	rw inv_comp_func_is_identity g_iso.f_func g_iso.f_injective at temp2,
	rw← temp2 at this,
	have temp3 := comp_identity f_iso.f_func,
	rw f_iso.f_domain at temp3,
	rw← g_iso.f_domain at temp3,
	rw temp3 at this,
	have temp4 := identity_comp g_iso.f_func,
	rw g_iso.f_range at temp4,
	rwa temp4 at this,
end

lemma order_isomorphism_unique' {A : ordered_set} (α : Set) [ordinal α] {f g : Set}
(f_iso : order_isomorphism f A.set A.r α (∈))
(g_iso : order_isomorphism g A.set A.r α (∈)) : f = g :=
order_isomorphism_unique _inst_1 f_iso g_iso


lemma set_func_of_class_func {φ : relation} {X : Set}
 (φ_func : class_function_on_set φ X) : ∃f, ∃(f_func : set_function f),
  domain f = X ∧ ∀⦃x : Set⦄ (y : Set), x ∈ X → (f @@ x = y ↔ φ x y) :=
begin
	 let ψ := λx y, ∃z, φ x z ∧ y = ord_pair x z,
	 have ψ_func : class_function_on_set ψ X,
	 {
		 fconstructor,
		 intros x hx,
		 cases φ_func.is_func hx with y hy,
		 use ord_pair x y,
		 use [y, hy.1],
		 intros z hxz,
		 cases hxz with z1 hz1,
		 rw hz1.2,
		 rw ord_pair_eq_iff,
		 use rfl,
		 exact hy.2 hz1.1,
	 },
	 cases restricted_replacement ψ_func with f hf,
	 use f,
	 
	suffices f_func : is_set_function f,
	{
		use set_function.mk f_func,
		have f_dom : domain f = X,
		{
		ext x,
			split,
			{
				intro h,
				rw mem_domain at h,
				cases h with y hy,
				rw hf (ord_pair x y) at hy,
				rcases hy with ⟨x2, hx2, hx2xy⟩,
				rcases hx2xy with ⟨z, hx2z, hx2hy⟩,
				rw ord_pair_eq_iff at hx2hy,
				rwa← hx2hy.1 at hx2,
			},
			{
				intros hx,
				rw mem_domain,
				cases φ_func.is_func hx with y hy,
				use y,
				rw hf,
				use [x, hx, y, hy.1],
			},
		},
		use f_dom,

		intros x y hx,
		split,
		{
			intro h,
			rw← f_dom at hx,
			have := func_spec {is_func := f_func} hx,
			rw hf at this,
			rcases this with ⟨x1, hx1, z, hx1z, hxx1⟩,
			rw ord_pair_eq_iff at hxx1,
			rw← hxx1.2 at hx1z,
			rw← hxx1.1 at hx1z,
			rwa h at hx1z,
		},
		{
			intro h,
			suffices : φ x (f @@ x),
			{
				cases φ_func.is_func hx with y1 hy1,
				rw← hy1.2 this,
				rw← hy1.2 h,
			},
			{
				rw← f_dom at hx,
				have := func_spec {is_func := f_func} hx,
				rw hf at this,
				rcases this with ⟨x1, hx1X, z, hx1z, hpair⟩,
				rw ord_pair_eq_iff at hpair,
				rwa [hpair.2, hpair.1],
			},
		},
	},

	intros p hp,
	rw hf at hp,
	rcases hp with ⟨x, hxX, z, hz⟩,
	use [z, x, hz.2],
	intros c hc,
	rw hf at hc,
	rcases hc with ⟨x1, hx1, z1, hz1φ, hpair⟩,
	rw ord_pair_eq_iff at hpair,
	rw← hpair.1 at hz1φ,
	rw← hpair.2 at hz1φ,
	cases φ_func.is_func hxX with y1 hy1,
	rw← hy1.2 hz1φ,
	rw← hy1.2 hz.1,
end

lemma order_iso_of_iso {f : Set} {A B : ordered_set} 
(f_iso : order_isomorphism f A.set A.r B.set B.r) : order_isomorphic A B :=
by use [f, f_iso]

lemma domain_restriction_subset {f : Set} (f_func : set_function f) (A : Set) :
domain (set_restriction f A) ⊆ domain f :=
begin 
	rw domain_of_restriction f A,
	exact pair_inter_subset_left (domain f) A,
end

lemma range_restriction_subset {f : Set} (f_func : set_function f) (A : Set) :
range (set_restriction f A) ⊆ range f :=
begin 
	intros y hy,
	rcases mem_range_is_func (is_func_restriction f_func A) hy with ⟨x, hx⟩,
	rw domain_of_restriction f A at hx,
	rw mem_pair_inter at hx,
	have := restriction_agrees f_func hx.1.2,
	rw← this at hx,
	rw mem_range_iff f_func,
	use [x, hx.1.1, eq.symm hx.2],
end

lemma restriction_injective {f : Set} (f_func : set_function f) (A : Set)
(f_inj : injective f) : injective (set_restriction f A) :=
begin 
	have rest_func := is_func_restriction f_func A,

	rw injective_iff rest_func,
	rw injective_iff f_func at f_inj,

	intros x y hx hy h,

	rw [domain_of_restriction, mem_pair_inter] at hx hy,
	rw [←restriction_agrees f_func hx.2, ←restriction_agrees f_func hy.2] at h,

	exact f_inj hx.1 hy.1 h,
end

theorem wo_isomorphic_ordinal {A : Set} {R : relation} (A_wo : well_order A R) :
∃! (α : Set), α ∈ ON ∧ order_isomorphic (ordered_set.mk α (∈)) (ordered_set.mk A R) :=
begin
	suffices h_exists : ∃(α : Set) (α_ord : ordinal α), 
	order_isomorphic (ordered_set.mk α (∈)) (ordered_set.mk A R),
	{
		unfold exists_unique,
		rcases h_exists with ⟨α, α_ord, hα⟩,
		use [α, α_ord, hα],

		intros β hβ,
		rcases order_isomorphism_equiv.tran hα (order_isomorphism_equiv.symm hβ.2)
		with ⟨f, f_iso, -⟩,
		apply eq.symm,
		rw← ordinals_isomorphic_iff_eq α_ord (ord_of_mem_ON hβ.1),
		use [f, f_iso],
	},
	let G := {a ∈ A | ∃(α : Set) [ordinal α]
	(f : Set) (f_iso : order_isomorphism f {c ∈ A | R c a} R α (∈)), true},
	let φ1 := λx y, 
	∃(f : Set) (f_iso : order_isomorphism f {c ∈ A | R c x} R y (∈)), y ∈ ON,
	have φ1_func : class_function_on_set φ1 G,
	{
		fconstructor,
		intros x hxG,
		rw mem_sep at hxG,
		rcases hxG with ⟨hxA, α, α_ord, f, f_iso, -⟩,
		use [α, f, f_iso, α_ord],
		intros z hz,
		rcases hz with ⟨f2, hf2, z_ord⟩,
		have hf2_inv := inverse_order_isomorphism hf2,
		have := order_isomorphism_comp hf2_inv f_iso,
		apply eq.symm,
		rw← ordinals_isomorphic_iff_eq (ord_of_mem_ON z_ord) α_ord,
		use [(f ∘ f2⁻¹), this],
	},

	rcases set_func_of_class_func φ1_func with ⟨f, f_func, f_dom, f_φ1⟩,

	let φ2 := λx y, 
	∃(y_iso : order_isomorphism y {c ∈ A | R c x} R (f @@ x) (∈)), true,
	have φ2_func : class_function_on_set φ2 G,
	{
		fconstructor,
		intros x hxG_temp,
		have hxG := hxG_temp,
		rw mem_sep at hxG_temp,
		rcases hxG_temp with ⟨hxa, α, α_ord, hₓ, hₓ_iso, -⟩,
		use hₓ,
		have hfα : f @@ x = α,
			{
				rw f_φ1 α hxG,
				use [hₓ, hₓ_iso],
				exact mem_ON_of_ord α_ord,
			},
		split,
		{
			rw← hfα at hₓ_iso,
			use hₓ_iso,
		},
		{
			intros z hz,
			rcases hz with ⟨z_iso, -⟩,
			rw hfα at z_iso,
			exact order_isomorphism_unique α_ord hₓ_iso z_iso,
		},
	},

	rcases set_func_of_class_func φ2_func with ⟨g, g_func, g_dom, g_φ2⟩,

	have hG : ∀⦃a c⦄, a ∈ G → c ∈ A → R c a → 
	(g @@ c = set_restriction (g @@ a) {x ∈ A | R x c} ∧ c ∈ G ∧ f @@ c = (g @@ a) @@ c),
	{
		intros a c haG hcA hca,
		let h_c := (set_restriction (g @@ a) {x ∈ A | R x c}),
		have hc_a_down : c ∈ {c ∈ A | R c a},
		{
			rw mem_sep,
			exact ⟨hcA, hca⟩,
		},
		have := (g_φ2 (g @@ a) haG).mp rfl,
		rcases this with ⟨g_iso, -⟩,
		have h_c_func : set_function h_c := is_func_restriction g_iso.f_func {x ∈ A | R x c},
		have hca_ss : {x ∈ A | R x c} ⊆ domain (g @@ a),
		{
			rw g_iso.f_domain,
			intros x hx,
			rw mem_sep at *,
			use hx.1,
			exact A_wo.tran hx.1 hcA haG.1 hx.2 hca,

		},

		have hc_g_dom : c ∈ domain (g @@ a),
		{
			rw g_iso.f_domain,
			rw mem_sep,
			exact ⟨hcA, hca⟩,
		},

		have fa_ord : f @@ a ∈ ON,
		{
			rcases (f_φ1 (f @@ a) haG).mp rfl with ⟨_, _, goal⟩,
			exact goal,
		},

		have : g @@ a @@ c ∈ f @@ a,
		{
			have := mem_range_of_mem_dom g_iso.f_func hc_g_dom,
			rwa g_iso.f_range at this,
		},
		have gac_ord := ord_of_mem_ON (mem_of_ordinal_is_ordinal fa_ord this),
		
		have h_c_dom :=
		@domain_of_restriction_ss (g @@ a) {x ∈ A | R x c} hca_ss g_iso.f_func,

		have h_c_iso : order_isomorphism h_c {x ∈ A | R x c} R ((g @@ a) @@ c) (∈) := 
		{
			f_func := h_c_func,
			f_domain := h_c_dom,
			f_range := begin 
				ext y,
				split,
				{
					intro h,
					rw mem_range_iff h_c_func at h,
					rcases h with ⟨x, hx, hxy⟩,
					rw @domain_of_restriction_ss
					(g @@ a) {x ∈ A | R x c} hca_ss g_iso.f_func at hx,
					have hx_c_down := hx,
					rw mem_sep at hx haG,
					have hx_a_down : x ∈ {c ∈ A | R c a},
					{
						rw mem_sep,
						use [hx.1, A_wo.tran hx.1 hcA haG.1 hx.2 hca],
					},
					rw← restriction_agrees g_iso.f_func hx_c_down at hxy,
					rw hxy,
					rw← g_iso.f_isomorphism hx_a_down hc_a_down,
					exact hx.2,
				},
				{
					intro h,
					rw mem_range_iff h_c_func,
					have : g @@ a @@ c ∈ f @@ a,
					{
						have := mem_range_of_mem_dom g_iso.f_func hc_g_dom,
						rwa g_iso.f_range at this,
					},
					have hy_fa := (ord_of_mem_ON fa_ord).tran this h,
					rw← g_iso.f_range at hy_fa,
					rw mem_range_iff g_iso.f_func at hy_fa,
					rcases hy_fa with ⟨x, hx_dom, hyx⟩,
					use x,
					rw h_c_dom,
					rw hyx at h,
					rw g_iso.f_domain at hx_dom,
					rw← g_iso.f_isomorphism hx_dom hc_a_down at h,
					have hx_c_down : x ∈ {x ∈ A | R x c},
					{
						rw mem_sep at hx_dom ⊢,
						use ⟨hx_dom.1, h⟩,
					},
					use hx_c_down,
					rw hyx,
					exact restriction_agrees g_iso.f_func hx_c_down,
				},
			end,
			f_injective := 
			restriction_injective g_iso.f_func {x ∈ A | R x c} g_iso.f_injective,
			f_isomorphism := begin 
				intros a1 a2 a1_dom a2_dom,
				have a1_c_down := a1_dom,
				have a2_c_down := a2_dom,
				rw mem_sep at a1_dom a2_dom haG,
				have ha1 : a1 ∈ {c ∈ A | R c a},
				{
					rw mem_sep,
					use a1_dom.1,
					exact A_wo.tran a1_dom.1 hcA haG.1 a1_dom.2 hca,
				},
				have ha2 : a2 ∈ {c ∈ A | R c a},
				{
					rw mem_sep,
					use a2_dom.1,
					exact A_wo.tran a2_dom.1 hcA haG.1 a2_dom.2 hca,
				},
				rw [←restriction_agrees g_iso.f_func a1_c_down, 
				←restriction_agrees g_iso.f_func a2_c_down],
				exact g_iso.f_isomorphism ha1 ha2,
			end,
		},

		have φ1_c : φ1 c (g @@ a @@ c),
		{
			use h_c,
			use h_c_iso,
			exact mem_ON_of_ord gac_ord,
		},
		have hcG : c ∈ G,
		{
			rw mem_sep,
			use [hcA, g @@ a @@ c, gac_ord, h_c, h_c_iso],
		},
		have hfc_gac := (f_φ1 (g @@ a @@ c) hcG).mpr φ1_c,
		have φ2_h_c : φ2 c h_c,
		{
			change 
			∃ (y_iso : order_isomorphism h_c {x ∈ A | R x c} R (f @@ c) has_mem.mem), true,
			rw hfc_gac,
			use h_c_iso,
		},
		have hgc_h_c := (g_φ2 h_c hcG).mpr φ2_h_c,
		exact ⟨hgc_h_c, hcG, hfc_gac⟩,
	},

	have ran_f_ord_set : subset_class (range f) ON,
	{
		intros α hα,
		rw mem_range_iff f_func at hα,
		rcases hα with ⟨a, haf, haα⟩,
		rw f_dom at haf,
		rcases (f_φ1 (f @@ a) haf).mp rfl with ⟨_, _, goal⟩,
		rw haα,
		exact goal,
	},

	have ran_f_tran : transitive (range f),
	{
		unfold transitive,
		intros α hα β hβ,
		rw mem_range_iff f_func at hα,
		rcases hα with ⟨a, haG, ha⟩,
		rw f_dom at haG,
		rw ha at hβ, clear ha,
		rw mem_range_iff f_func,
		rcases (g_φ2 (g @@ a) haG).mp rfl with ⟨ga_iso, -⟩,
		rw← ga_iso.f_range at hβ,
		rw mem_range_iff ga_iso.f_func at hβ,
		rcases hβ with ⟨b, hb_a_down, hbβ⟩,
		have hb_f_dom := hb_a_down,
		rw ga_iso.f_domain at hb_a_down,
		rw mem_sep at hb_a_down,
		have := hG haG hb_a_down.1 hb_a_down.2,
		rw← this.2.2 at hbβ,
		rw f_dom,
		use [b, this.2.1, hbβ],
	},

	have ran_f_ord := tran_set_of_ord_is_ord ran_f_tran ran_f_ord_set,
	have f_order_preserving_mp : ∀⦃a b⦄, a ∈ G → b ∈ G → R b a → (f @@ b) ∈ (f @@ a),
	{
		intros a b haG hbG hba,
		have hbA := hbG, rw mem_sep at hbA,
		rw (hG haG hbA.1 hba).2.2,
		rcases (g_φ2 (g @@ a) haG).mp rfl with ⟨ga_iso, -⟩,
		rw [←ga_iso.f_range, mem_range_iff ga_iso.f_func, ga_iso.f_domain],
		use b,
		rw mem_sep,
		use ⟨⟨hbA.1, hba⟩, rfl⟩,
	},
	have f_order_preserving : ∀⦃a b⦄, b ∈ G → a ∈ G → (R b a ↔ (f @@ b) ∈ (f @@ a)),
	{
		intros a b hbG haG,
		split,
		{
			intro hba,
			exact f_order_preserving_mp haG hbG hba,
		},
		{
			intro h,
			by_contra hba,
			have haA : a ∈ A,
			{
				rw mem_sep at haG, exact haG.1,
			},
			have hbA : b ∈ A,
			{
				rw mem_sep at hbG, exact hbG.1,
			},
			have fa_ord : ordinal (f @@ a),
			{
				apply ord_of_mem_ON,
				apply ran_f_ord_set,
				rw mem_range_iff f_func,
				use a,
				rw f_dom,
				use haG,
			},
			cases A_wo.tri hbA haA, exact hba h_1,
			cases h_1,
			{
				have := f_order_preserving_mp hbG haG h_1,
				exact not_ord_mem_ord fa_ord this h,
			},
			{
				rw h_1 at h,
				exact ord_not_mem_self (mem_ON_of_ord fa_ord) h,
			},
		},
	},
	have f_iso : order_isomorphism f G R (range f) (∈) := {
		f_func := f_func,
		f_domain := f_dom,
		f_range := rfl,
		f_injective := begin 
			rw [injective_iff f_func, f_dom],
			intros x y hxG hyG hxy,
			by_contra,
			have hxA : x ∈ A,
			{
				rw mem_sep at hxG,
				exact hxG.1,
			},
			have hyA : y ∈ A,
			{
				rw mem_sep at hyG,
				exact hyG.1,
			},
			have fx_ord : ordinal (f @@ x),
			{
				apply ord_of_mem_ON,
				apply ran_f_ord_set,
				rw mem_range_iff f_func,
				use x,
				rw f_dom,
				use hxG,
			},
			cases A_wo.tri hxA hyA,
			{
				have := f_order_preserving_mp hyG hxG h_1,
				rw← hxy at this,
				exact ord_not_mem_self (mem_ON_of_ord fx_ord) this,
			},
			cases h_1,
			{
				have := f_order_preserving_mp hxG hyG h_1,
				rw← hxy at this,
				exact ord_not_mem_self (mem_ON_of_ord fx_ord) this,
			},
			{
				exact h h_1,
			},
		end,
		f_isomorphism := λb a, @f_order_preserving a b,
	},

	by_cases hGA : A \ G ≠ ∅,
	{
		rcases A_wo.wf (diff_subset A G) hGA with ⟨e, e_AG, e_min⟩,
		have heG : {a ∈ A | R a e} = G,
		{
			ext a,
			rw mem_sep,
			split,
			{
				intro h,
				by_contra haG,
				have : a ∈ A \ G,
				{
					rw mem_diff,
					exact ⟨h.1, haG⟩,
				},
				exact e_min this h.2,
			},
			{
				intro haG_temp,
				have haG := haG_temp,
				rw mem_sep at haG_temp,
				use haG_temp.1,
				rw mem_diff at e_AG,
				cases A_wo.tri haG_temp.1 e_AG.1, exact h,
				cases h,
				{
					exfalso,
					exact e_AG.2 (hG haG e_AG.1 h).2.1,
				},
				{
					rw h at haG, exfalso,
					exact e_AG.2 haG,
				},
			},
		},
		suffices : e ∈ G,
		{
			rw mem_diff at e_AG, exfalso,
			exact e_AG.2 this,
		},
		{
			rw mem_sep,
			rw mem_diff at e_AG,
			use e_AG.1,
			use [range f, ran_f_ord, f],
			rw heG,
			use f_iso,
		},
	},
	{
		have : A = G,
		{
			rw eq_iff_subsets,
			split,
			{
				intros a ha,
				by_contra,
				have : a ∈ A \ G,
				{
					rw mem_diff,
					exact ⟨ha, h⟩,
				},
				push_neg at hGA,
				rw hGA at this,
				simp at this,
				exact this,
			},
			{
				intros a haG,
				rw mem_sep at haG,
				exact haG.1,
			},
		},
		use [range f, ran_f_ord],
		unfold order_isomorphic,
		have inv_iso := inverse_order_isomorphism f_iso,
		use f⁻¹,
		rw← this at inv_iso,
		use inv_iso,
	},
end

lemma wo_of_is_wo {A : Set} {R : relation} (is_wo : is_well_order A R) : 
well_order A R := classical.some (classical.exists_true_of_nonempty is_wo)

lemma is_wo_of_wo {A : Set} {R : relation} (A_wo : well_order A R) :
is_well_order A R := nonempty.intro A_wo

lemma wo_of_order_isomorphic_to_wo {A B : Set} {r1 r2 : relation} (A_wo : well_order A r1)
{f : Set} (f_iso : order_isomorphism f B r2 A r1) : well_order B r2 :=
{
	irrfl := begin 
		intros x hxB hx,
		rw f_iso.f_isomorphism hxB hxB at hx,
		have : ∀⦃a⦄, a ∈ B → f @@ a ∈ A,
		{
			intros a haB,
			rw← f_iso.f_domain at haB,
			rw← f_iso.f_range,
			rw mem_range_iff f_iso.f_func,
			use [a, haB],
		},
		exact A_wo.irrfl (this hxB) hx,
	end,
	tran := begin
		have : ∀⦃a⦄, a ∈ B → f @@ a ∈ A,
		{
			intros a haB,
			rw← f_iso.f_domain at haB,
			rw← f_iso.f_range,
			rw mem_range_iff f_iso.f_func,
			use [a, haB],
		},

		intros a b c a_dom b_dom c_dom hab hbc,
		rw f_iso.f_isomorphism a_dom b_dom at hab,
		rw f_iso.f_isomorphism b_dom c_dom at hbc,

		rw f_iso.f_isomorphism a_dom c_dom,
		exact A_wo.tran (this a_dom) (this b_dom) (this c_dom) hab hbc,
	end,
	tri := begin
		have : ∀⦃a⦄, a ∈ B → f @@ a ∈ A,
		{
			intros a haB,
			rw← f_iso.f_domain at haB,
			rw← f_iso.f_range,
			rw mem_range_iff f_iso.f_func,
			use [a, haB],
		},
		intros a b a_dom b_dom,
		rw f_iso.f_isomorphism a_dom b_dom,
		rw f_iso.f_isomorphism b_dom a_dom,
		have := A_wo.tri (this a_dom) (this b_dom),
		have inj := f_iso.f_injective,
		rw injective_iff f_iso.f_func at inj,
		rw← f_iso.f_domain at a_dom b_dom,
		have := inj a_dom b_dom,
		tauto,
	end,
	wf := begin 
		have f_A : ∀⦃a⦄, a ∈ B → f @@ a ∈ A,
		{
			intros a haB,
			rw← f_iso.f_domain at haB,
			rw← f_iso.f_range,
			rw mem_range_iff f_iso.f_func,
			use [a, haB],
		},
		intros Y Y_ss Y_nonempty,
		let X := {a ∈ A | ∃b ∈ Y, f @@ b = a},
		have X_nonempty : X ≠ ∅,
		{
			intro h,
			cases nonempty_has_mem Y_nonempty with b hb,
			have : f @@ b ∈ X,
			{
				rw mem_sep,
				use [f_A (Y_ss hb), b, hb],
			},

			rw h at this,
			exact not_mem_empty this,
		},
		have X_ss : X ⊆ A,
		{
			intros x hx,
			rw mem_sep at hx,
			rcases hx with ⟨x_A, b, hb, hxb⟩,
			rw← hxb,
			exact f_A (Y_ss hb),
		},

		rcases A_wo.wf X_ss X_nonempty with ⟨a, a_X, ha⟩,
		rw mem_sep at a_X,
		rcases a_X with ⟨a_X, b, b_Y, hab⟩,
		use [b, b_Y],
		intros c c_Y hc,
		rw f_iso.f_isomorphism (Y_ss c_Y) (Y_ss b_Y) at hc,
		rw hab at hc,
		have fc_X : f @@ c ∈ X,
		{
			rw mem_sep,
			use [f_A (Y_ss c_Y), c, c_Y],
		},
		exact ha fc_X hc,
	end,
}

def type (A : Set) (R : relation) : Set :=
if is_wo : is_well_order A R then 
classical.some (exists_of_exists_unique (wo_isomorphic_ordinal (wo_of_is_wo is_wo)))
else ∅

lemma type_if {A : Set} {R : relation} (A_wo : well_order A R) : type A R =
classical.some
(exists_of_exists_unique (wo_isomorphic_ordinal A_wo)) :=
dif_pos (is_wo_of_wo A_wo)

lemma type_spec {A : Set} {R : relation} (A_wo : well_order A R) : 
(type A R) ∈ ON ∧ order_isomorphic {set := type A R, r := (∈)} 
{set := A, r := R} :=
begin 
	have if_in := type_if A_wo,
	have := 
	classical.some_spec (exists_of_exists_unique (wo_isomorphic_ordinal A_wo)),
	rw← if_in at this,
	exact this,
end

lemma type_is_isomorphic {A : Set} {R : relation} (A_wo : well_order A R) :
order_isomorphic (ordered_set.mk (type A R) (∈)) (ordered_set.mk A R) :=
(type_spec A_wo).2

lemma type_ord (A : Set) (R : relation) : ordinal (type A R) :=
begin 
	by_cases is_A_wo : is_well_order A R,
	{exact ord_of_mem_ON (type_spec (wo_of_is_wo is_A_wo)).1},
	{
		have : type A R = ∅ := dif_neg is_A_wo,
		rw this,
		exact empty_is_ordinal,
	},
end 

def type_isomorphism {A : Set} {R : relation} (A_wo : well_order A R) :
Set := inv (classical.some (type_spec A_wo).2)

def type_isomorphism_spec {A : Set} {R : relation} (A_wo : well_order A R) :=
classical.some_spec (type_spec A_wo).2

lemma type_iso {A : Set} {R : relation} (A_wo : well_order A R) :
order_isomorphism (type_isomorphism A_wo) A R (type A R) (∈) :=
(inverse_order_isomorphism (classical.some (type_isomorphism_spec A_wo)))

lemma type_unique {A : Set} {R : relation} {f α : Set}
(α_ord : ordinal α) (f_iso : order_isomorphism f A R α (∈)) : α = type A R :=
begin
	have A_wo := wo_of_order_isomorphic_to_wo α_ord.wo f_iso,
	have h := (wo_isomorphic_ordinal A_wo),
	unfold exists_unique at h,
	rcases h with ⟨β, hβ, h⟩,
	have α1 : order_isomorphic 
	{set := α, r := (∈)} {set := A, r := R},
	{
		unfold order_isomorphic,
		dsimp only,
		use (inv f),
		use inverse_order_isomorphism f_iso,
	},

	rw h α ⟨mem_ON_of_ord α_ord, α1⟩,
	exact eq.symm 
	(h (type A R) ⟨mem_ON_of_ord (type_ord A R), type_is_isomorphic A_wo⟩),
end

lemma type_unique' {A B f : Set} {r1 r2 : relation} 
(f_iso : order_isomorphism f A r1 B r2) : type A r1 = type B r2 :=
begin 
	by_cases is_A_wo : is_well_order A r1,
	{
		have invf_iso := (inverse_order_isomorphism f_iso),

		have A_wo := wo_of_is_wo is_A_wo,
		have B_wo := wo_of_order_isomorphic_to_wo A_wo invf_iso,

		have A_type_iso := type_iso A_wo,

		have B_iso := order_isomorphism_comp invf_iso A_type_iso,

		have typeA_ord := type_ord A r1,
		exact type_unique typeA_ord B_iso,
	},
	{
		have A_empty : type A r1 = ∅ := dif_neg is_A_wo,
		rw A_empty,

		have neg_B_wo : ¬is_well_order B r2 :=
		λh, is_A_wo (is_wo_of_wo (wo_of_order_isomorphic_to_wo (wo_of_is_wo h) f_iso)),

		have B_empty : type B r2 = ∅ := dif_neg neg_B_wo,
		rw B_empty,
	},
end

lemma type_of_ord {α : Set} (α_ord : ordinal α) : type α (∈) = α :=
eq.symm (type_unique α_ord (ord_isomorphism_self α (∈)))

lemma type_of_type (A : Set) (R : relation) : type (type A R) (∈) = type A R :=
type_of_ord (type_ord A R)

lemma type_eq_iff {A B : Set} {r1 r2 : relation} (A_wo : well_order A r1) 
(B_wo : well_order B r2) : 
type A r1 = type B r2 ↔ order_isomorphic {set := A, r := r1} {set := B, r := r2} :=
begin 
	split,
	{
		intro h,

		have A_type_iso := type_iso A_wo,
		have B_type_iso := type_iso B_wo,
		rw h at A_type_iso,

		have B_inv := inverse_order_isomorphism (B_type_iso),
		have f_iso := order_isomorphism_comp A_type_iso B_inv,

		use [((type_isomorphism B_wo)⁻¹ ∘ type_isomorphism A_wo), f_iso],
	},
	{
		intro h,
		rcases h with ⟨f, f_iso, -⟩,
		exact type_unique' f_iso,
	},
end

instance : has_zero Set := ⟨∅⟩
instance : has_one Set := ⟨succ ∅⟩


def ord_sum (α β : Set) : Set := 
type ((sing ∅ × α) ∪ (sing 1 × β)) 
(dict_order (∈) (∈))

instance : has_add Set := ⟨λ a b, ord_sum a b⟩

def ord_sum_set (α β : Set) : Set := (sing ∅ × α) ∪ (sing 1 × β)
def ord_sum_order (α β : Set) := (dict_order (∈) (∈))

lemma wo_of_sing {x : Set} {R : relation} (h : ¬R x x) : well_order (sing x) (R) :=
{
	irrfl := begin 
		intros y hy,
		rw mem_sing at hy,
		rwa hy,
	end,
	tran := begin 
		intros a b c ha hb hc hab hbc,
		exfalso,
		rw mem_sing at *,
		rw [ha, hb] at hab,
		exact h hab,
	end,
	tri := begin 
		intros a b ha hb,
		rw mem_sing at *,
		finish,
	end,
	wf := begin 
		intros X X_ss X_nonempty,
		use x,
		cases nonempty_has_mem X_nonempty with y hy,
		have := X_ss hy,
		rw mem_sing at this,
		rw← this,
		use hy,

		intros a ha,
		have t1 := X_ss ha,
		rw mem_sing at t1,
		rw [t1, this],
		exact h,
	end,
}

lemma one_ord : ordinal (1:Set) := succ_of_ordinal_is_ordinal empty_is_ordinal

lemma wo_of_ord_sum_set {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) :
 well_order (ord_sum_set α β) (ord_sum_order α β) :=
begin 
	have h_ss : ord_sum_set α β ⊆ ((succ 1) × (α ∪ β)),
	{
		intros p hp,
		unfold ord_sum_set at hp,
		rw mem_pair_union at hp,
		rw mem_prod,
		cases hp,
		{
			rw mem_prod at hp,
			rcases hp with ⟨a, b, ha, hb, hab⟩,
			rw mem_sing at ha,
			use [a, b],
			rw ha at *,
			have t1 := (lt_succ_self ∅),
			have t2 := (lt_succ_self (succ ∅)),
			have ss_ord := succ_of_ordinal_is_ordinal 
			(succ_of_ordinal_is_ordinal (empty_is_ordinal)),
			use ss_ord.tran t2 t1,
			rw mem_pair_union,
			exact ⟨or.inl hb, hab⟩,
		},
		{
			rw mem_prod at hp,
			rcases hp with ⟨a, b, ha, hb, hab⟩,
			rw mem_sing at ha,
			use [a, b],
			rw ha at *,
			use lt_succ_self (succ ∅),
			rw mem_pair_union,
			exact ⟨or.inr hb, hab⟩,
		},
	},

	exact wo_of_is_wo 
	(subset_of_wo_is_wo h_ss 
	(dict_wo (succ_of_ordinal_is_ordinal (one_ord)).wo (pair_union_ordinal α_ord β_ord).wo)),
end

lemma ord_of_ord_sum (α β : Set) :
ordinal (α + β) := by apply type_ord

def ord_prod (α β : Set) : Set := type (β × α) (dict_order (∈) (∈))
instance : has_mul Set := ⟨λ a b, ord_prod a b⟩

def ord_prod_set (α β : Set) : Set := β × α
def ord_prod_order (α β : Set):= dict_order (∈) (∈)

lemma ord_prod_is_ord (α β : Set) :
ordinal (α * β) := by apply type_ord

lemma prod_empty (X : Set) : X × ∅ = ∅ :=
begin 
		ext x,
		split,
		{
			intro h,
			rw mem_prod at h,
			rcases h with ⟨a, b, ha, hb⟩,
			exfalso,
			exact not_mem_empty hb.1,
		},
		{
			intro h, exfalso,
			exact not_mem_empty h,
		},
end

lemma union_empty (X : Set) : X ∪ ∅ = X :=
begin 
	ext x,
	rw mem_pair_union,
	split,
	{
		intro h,
		cases h,
		{exact h},
		{
			exfalso,
			exact not_mem_empty h,
		},
	},
	{exact λh, or.inl h},
end

lemma ord_sum_zero {α : Set} (α_ord : ordinal α) : α + 0 = α :=
begin 
	unfold has_add.add ord_sum has_zero.zero,
	rw [prod_empty, union_empty],

	have h_iso : order_isomorphic {set := α, r := (∈)}
	{set := sing ∅ × α, r := dict_order has_mem.mem has_mem.mem},
	{
		let φ := λx y, y = ord_pair ∅ x,
		have φ_func : class_function_on_set φ α,
		{
			fconstructor,
			intros x hx,
			use ord_pair ∅ x,
			use rfl,
			intros z hz,
			exact eq.symm hz,
		},
		rcases set_func_of_class_func φ_func with ⟨f, f_func, f_dom, f_φ⟩,
		have f_iso : order_isomorphism f α (∈) (sing ∅ × α) 
		(dict_order (∈) (∈)) :=
		{
			f_func := f_func,
			f_domain := f_dom,
			f_range := begin
				ext y,
				rw mem_range_iff f_func,
				split,
				{
					intro h,
					rcases h with ⟨x, x_dom, hxy⟩,
					rw f_dom at x_dom,
					have := (f_φ y x_dom).mp (eq.symm hxy),
					rw mem_prod,
					use [∅, x],
					rw mem_sing,
					use [rfl, x_dom],
					exact this,
				},
				{
					intro h,
					rw mem_prod at h,
					rcases h with ⟨a, b, ha, hb, hab⟩,
					rw mem_sing at ha,
					rw ha at hab,
					rw← f_dom at hb,
					use [b, hb],
					rw f_dom at hb,
					apply eq.symm,
					rw f_φ y hb,
					exact hab,
				},
			end,
			f_injective := begin 
				rw injective_iff f_func,
				intros x1 x2 hx1 hx2 hx1x2,
				rw← f_dom at f_φ,
				have t1 := (f_φ (f @@ x1) hx1).mp rfl,
				have t2 := (f_φ (f @@ x2) hx2).mp rfl,
				rw hx1x2 at t1,
				change f @@ x2 = ord_pair ∅ x1 at t1,
				change f @@ x2 = ord_pair ∅ x2 at t2,
				rw t1 at t2,
				rw ord_pair_eq_iff at t2,
				exact t2.2,
			end,
			f_isomorphism := begin
				intros a1 a2 a1_dom a2_dom,

				have t1 := (f_φ (f @@ a1) a1_dom).mp rfl,
				have t2 := (f_φ (f @@ a2) a2_dom).mp rfl,

				change f @@ a1 = ord_pair ∅ a1 at t1,
				change f @@ a2 = ord_pair ∅ a2 at t2,

				split,
				{
					intro h,
					use [∅, a1, ∅, a2],
					use [t1, t2, or.inr ⟨rfl, h⟩],
				},
				{
					intro h,
					unfold dict_order at h,
					rcases h with ⟨a, b, a', b', hab, hab', horder⟩,
					rw t1 at hab,
					rw t2 at hab',
					rw ord_pair_eq_iff at hab hab',
					cases horder,
					{
						rw← hab'.1 at horder, exfalso,
						exact not_mem_empty horder,
					},
					{
						rw [hab.2, hab'.2],
						exact horder.2,
					},
				},
			end
		},
		fconstructor, use f,
		dsimp only,
		use f_iso,
	},

	rcases h_iso with ⟨f, f_iso, -⟩,
	exact eq.symm (type_unique α_ord (inverse_order_isomorphism f_iso)),
end

lemma zero_ne_one : (0:Set) ≠ 1 :=
begin 
	intro h,
	unfold has_zero.zero has_one.one at h,
	have := lt_succ_self ∅,
	unfold has_lt.lt at this,
	rw← h at this,
	exact not_mem_empty this,
end

lemma succ_increasing {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α < β ↔
succ α < succ β := 
begin
	have sα_ord := succ_of_ordinal_is_ordinal α_ord,
	have sβ_ord := succ_of_ordinal_is_ordinal β_ord,

	split,
	{
		intro h,
		cases ON_ordinal_class.wo.tri (mem_ON_of_ord (sα_ord)) (mem_ON_of_ord (sβ_ord)),
		{exact h_1},
		cases h_1,
		{
			unfold has_lt.lt at *,
			exfalso,
			rw mem_succ at h_1,
			cases h_1,
			{exact not_ord_mem_ord α_ord h (α_ord.tran h_1 (lt_succ_self β))},
			{
				rw← h_1 at h,
				exact not_ord_mem_ord β_ord (lt_succ_self β) h,
			},
		},
		{
			exfalso,
			rw succ_inj_on_ON α_ord h_1 at h,
			exact ord_not_mem_self (mem_ON_of_ord β_ord) h,
		},
	},
	{
		unfold has_lt.lt,
		intro h,
		rw mem_succ at h,
		cases h,
		{exact β_ord.tran h (lt_succ_self α)},
		{
			rw← h,
			exact lt_succ_self α,
		},
	}
end

lemma succ_increasing' {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α ≤ β ↔
succ α ≤ succ β := 
begin 
	split,
	{
		intro h,
		cases h,
		{exact or.inl ((succ_increasing α_ord β_ord).mp h)},
		{exact or.inr (congr_arg succ h)},
	},
	{
		intro h,
		cases h,
		{exact or.inl ((succ_increasing α_ord β_ord).mpr h)},
		{exact or.inr (succ_inj_on_ON α_ord h)},
	},
end

lemma subset_ON_of_subset_ord {X α : Set} (α_ord : ordinal α) (X_ss : X ⊆ α) : 
subset_class X ON := λβ hβ, mem_of_ordinal_is_ordinal (mem_ON_of_ord α_ord) (X_ss hβ)

lemma ord_not_lt_of_le {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α ≤ β → ¬β < α :=
ord_not_lt_iff.mpr

lemma ord_not_le_of_lt {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α < β → ¬β ≤ α :=
(ord_not_le_iff β α).mpr

lemma ord_lt_of_not_le {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : ¬α ≤ β → β < α :=
(ord_not_le_iff α β).mp

lemma ord_lt_of_le_of_lt {α β γ : Set}
(γ_ord : ordinal γ) : α ≤ β → β < γ → α < γ :=
begin 
	intros hab hby,
	cases hab,
	{exact γ_ord.tran hby hab},
	{
		rw hab,
		exact hby,
	},
end

lemma ord_lt_of_lt_of_le {α β γ : Set}
(γ_ord : ordinal γ) : α < β → β ≤ γ → α < γ :=
begin 
	intros hab hby,
	cases hby,
	{exact γ_ord.tran hby hab},
	{
		rw← hby,
		exact hab,
	},
end

lemma ord_lt_of_lt_of_lt {α β γ : Set}
(γ_ord : ordinal γ) : α < β → β < γ → α < γ := λhab hby, γ_ord.tran hby hab

lemma le_of_lt_succ : ∀{a b : Set}, a < succ b → a ≤ b :=
begin 
	intros a b hab,
	unfold has_lt.lt has_le.le at *,
	rw mem_succ at hab,
	exact hab,
end

lemma mem_range_of_mem_domain {f x : Set} (f_func : set_function f) (x_dom : x ∈ domain f) :
f @@ x ∈ range f := mem_range_of_mem_dom f_func x_dom

lemma type_le_of_subset {α X : Set} (α_ord : ordinal α) (X_ss : X ⊆ α) :
type X (∈) ≤ α :=
begin 
	have X_wo := wo_of_is_wo (subset_of_wo_is_wo X_ss α_ord.wo),
	have f_iso := inverse_order_isomorphism (type_iso X_wo),
	set f := (type_isomorphism X_wo)⁻¹,

	have f_ord : ∀x, ordinal (f @@ x),
	{
		intro x,
		by_cases x ∈ domain f,
		{
			have := mem_range_of_mem_dom f_iso.f_func h,
			rw f_iso.f_range at this,
			use ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord α_ord) (X_ss this)),
		},
		{
			rw func_out (@not_and_of_not_right (is_set_function f) (x ∈ domain f) h),
			use empty_is_ordinal,
		},
	},

	suffices hf : ∀⦃ξ⦄, ξ ∈ type X (∈) → ξ ≤ (f @@ ξ),
	{
		rw← le_iff_subset (mem_ON_of_ord (type_ord X (∈))) (mem_ON_of_ord α_ord),
		intros β hβ,
		have t1 := hf hβ,
		have t2 : f @@ β ∈ X,
		{
			rw← f_iso.f_range,
			rw mem_range_iff f_iso.f_func,
			rw f_iso.f_domain,
			exact ⟨β, hβ, rfl⟩,
		},

		have fβ_ord : ordinal (f @@ β) :=
		ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord α_ord) (X_ss t2)),

		unfold has_le.le at t1,
		cases t1,
		{exact α_ord.tran (X_ss t2) t1},
		{
			rw t1,
			exact X_ss t2,
		},
	},

	by_cases h_empty : {ξ ∈ type X (∈) | f @@ ξ < ξ} = ∅,
	{
		intros ξ hξ,
		by_contra,

		have fξ_ord := f_ord ξ,

		have ξ_ord : ordinal ξ :=
		ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord (type_ord X (∈))) hξ),

		rw @ord_not_le_iff ξ (f @@ ξ) ξ_ord fξ_ord at h,

		have contra : ξ ∈ {ξ ∈ type X (∈) | f @@ ξ < ξ},
		{
			rw mem_sep,
			exact ⟨hξ, h⟩,
		},

		rw h_empty at contra,
		exact not_mem_empty contra,
	},

	exfalso,

	have h_ss_ON : subset_class {ξ ∈ type X (∈) | (f @@ ξ) < ξ} ON,
	{
		intros β hβ,
		rw mem_sep at hβ,
		exact mem_of_ordinal_is_ordinal (mem_ON_of_ord (type_ord X (∈))) hβ.1,
	},

	rcases ON_ordinal_class.wo.wf h_ss_ON h_empty with ⟨ξ, hξ, ξ_min⟩,
	have hξ_sep : ξ ∈ type X has_mem.mem ∧ f @@ ξ < ξ := by rwa mem_sep at hξ,
	have ξ_ord  := 
	ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord (type_ord X (∈))) hξ_sep.1),

	have h_lt_ξ : ∀{β}, β ∈ ξ → β ≤ (f @@ β),
	{
		intros β hβ,
		by_contra,
		have β_ord := ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord ξ_ord) hβ),
		have hβ_X := ((type_ord X (∈)).tran hξ_sep.1 hβ),

		have contra := ord_lt_of_not_le β_ord (f_ord β) h,
		have : β ∈ {ξ ∈ type X has_mem.mem | f @@ ξ < ξ},
		{
			rw mem_sep,
			exact ⟨hβ_X, contra⟩,
		},

		exact ξ_min this hβ,
	},

	have hfξ_X : (f @@ ξ) ∈ type X (∈) := (type_ord X (∈)).tran hξ_sep.1 hξ_sep.2,

	have contra1 := (f_iso.f_isomorphism hfξ_X hξ_sep.1).mp hξ_sep.2,
	have contra2 := h_lt_ξ hξ_sep.2,

	exact ord_not_le_of_lt (f_ord (f @@ ξ)) (f_ord ξ) contra1 contra2,
end

lemma restriction_isomorphism {A B f : Set} {r1 r2 : relation} 
(f_iso : order_isomorphism f A r1 B r2) (X : Set) :
 order_isomorphism (set_restriction f (X ∩ A)) 
 (X ∩ A) r1 (range (set_restriction f (X ∩ A))) r2 :=
{
	f_func := is_func_restriction f_iso.f_func (X ∩ A),
	f_domain := begin 
		rw [@domain_of_restriction f (X ∩ A) f_iso.f_func, f_iso.f_domain],
		ext x,
		rw [mem_pair_inter, mem_pair_inter],
		tauto,
	end,
	f_range := rfl,
	f_injective := begin 
		rw injective_iff (is_func_restriction f_iso.f_func (X ∩ A)),
		intros x y x_dom y_dom hxy,
		have h_dom : domain (set_restriction f (X ∩ A)) = X ∩ A,
		{
			rw [@domain_of_restriction f (X ∩ A) f_iso.f_func, f_iso.f_domain],
			ext x,
			rw [mem_pair_inter, mem_pair_inter],
			tauto,
		},

		rw h_dom at x_dom y_dom,
		rw← restriction_agrees f_iso.f_func x_dom at hxy,
		rw← restriction_agrees f_iso.f_func y_dom at hxy,

		have h_ss := pair_inter_subset_right X A,
		rw← f_iso.f_domain at *,

		have := f_iso.f_injective,
		rw injective_iff f_iso.f_func at this,
		exact this (h_ss x_dom) (h_ss y_dom) hxy,
	end,
	f_isomorphism := begin 
		intros x y x_dom y_dom,

		have h_ss := pair_inter_subset_right X A,

		rw← restriction_agrees f_iso.f_func x_dom,
		rw← restriction_agrees f_iso.f_func y_dom,
		exact f_iso.f_isomorphism (h_ss x_dom) (h_ss y_dom),
	end
}

lemma type_le_of_subset_wo {A X : Set} {R : relation} (A_wo : well_order A R) (X_ss : X ⊆ A) :
type X R ≤ type A R :=
begin 
	have f_isoA := type_iso A_wo,
	set f := (type_isomorphism A_wo),

	have h_inter : X ∩ A = X,
	{
		rw eq_iff_subsets,
		split,
		{exact pair_inter_subset_left X A},
		{
			intros x hx,
			rw mem_pair_inter,
			exact ⟨hx, X_ss hx⟩,
		},
	},

	have f_isoX := restriction_isomorphism f_isoA X,
	rw h_inter at f_isoX,

	have h_range := range_restriction_subset f_isoA.f_func X,
	rw f_isoA.f_range at h_range,

	rw type_unique' f_isoX,
	exact type_le_of_subset (type_ord A R) h_range,
end

lemma ord_le_iff_ss {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α ≤ β ↔ α ⊆ β :=
(le_iff_subset (mem_ON_of_ord α_ord) (mem_ON_of_ord β_ord)).symm

lemma le_sum_right {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : β ≤ α + β :=
begin
	let φ := λx y, y = ord_pair 1 x,
	have φ_func : class_function_on_set φ β,
	{
		fconstructor,
		intros x hx,
		use [ord_pair 1 x, rfl, λz hz, eq.symm hz],
	},

	rcases set_func_of_class_func φ_func with ⟨f, f_func, f_domain, hfφ⟩,

	have f_iso : order_isomorphism f β (∈) (sing 1 × β) (dict_order (∈) (∈)) :=
	{
		f_func := f_func,
		f_domain := f_domain,
		f_range := begin
			ext y,
			rw mem_range_iff f_func,
			split,
			{
				intro h,
				rcases h with ⟨x, x_dom, hxf⟩,
				rw hxf,
				rw← f_domain at hfφ,
				have := (hfφ (f @@ x) x_dom).mp rfl,
				change f @@ x = ord_pair 1 x at this,
				rw [this, mem_prod_pair, mem_sing],
				rw f_domain at x_dom,
				exact ⟨rfl, x_dom⟩,				
			},
			{
				intro h,
				rw mem_prod at h,
				rcases h with ⟨a, b, ha, hb, hab⟩,
				rw mem_sing at ha,
				rw ha at *,
				rw f_domain,
				use [b, hb],
				rw hab,
				exact eq.symm ((hfφ (f @@ b) hb).mp rfl),
			},
		end,
		f_injective := begin 
			rw injective_iff f_func,
			intros x y x_dom y_dom hfxy,
			rw← f_domain at hfφ,

			have hfx := (hfφ (f @@ x) x_dom).mp rfl,
			have hfy := (hfφ (f @@ y) y_dom).mp rfl,

			change f @@ x = ord_pair 1 x at hfx,
			change f @@ y = ord_pair 1 y at hfy,
			
			rw hfx at hfxy,
			rw hfy at hfxy,

			rw ord_pair_eq_iff at hfxy,
			exact hfxy.2,
		end,
		f_isomorphism := begin 
			intros x y x_dom y_dom,

			have hfx := (hfφ (f @@ x) x_dom).mp rfl,
			have hfy := (hfφ (f @@ y) y_dom).mp rfl,

			change f @@ x = ord_pair 1 x at hfx,
			change f @@ y = ord_pair 1 y at hfy,

			rw [hfx, hfy],
			rw dict_pair has_mem.mem has_mem.mem,
			have temp : ¬((1:Set) ∈ (1:Set)),
			{
				intro h,
				unfold has_one.one at h,
				have := succ_increasing empty_is_ordinal empty_is_ordinal,
				unfold has_lt.lt at this,
				rw← this at h,
				exact not_mem_empty h,
			},
			simp [temp],
		end
	},

	have h_ss : (sing 1 × β) ⊆ ord_sum_set α β,
	{
		intros x hx,
		unfold ord_sum_set,
		rw mem_pair_union,
		exact or.inr hx,
	},

	have h_ord := (type_ord (ord_sum_set α β) (ord_sum_order α β)),
	have h_wo : well_order (ord_sum_set α β) (ord_sum_order α β)
	:= wo_of_ord_sum_set α_ord β_ord,

	have := type_le_of_subset_wo h_wo h_ss,
	unfold ord_sum_order at this,
	rw ←type_unique' f_iso at this,
	unfold has_add.add ord_sum,
	rw type_of_ord β_ord at this,
	exact this,
end

lemma le_sum_left {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) : α ≤ α + β :=
begin
	let φ := λx y, y = ord_pair 0 x,
	have φ_func : class_function_on_set φ α,
	{
		fconstructor,
		intros x hx,
		use [ord_pair 0 x, rfl, λz hz, eq.symm hz],
	},

	rcases set_func_of_class_func φ_func with ⟨f, f_func, f_domain, hfφ⟩,

	have f_iso : order_isomorphism f α (∈) (sing 0 × α) (dict_order (∈) (∈)) :=
	{
		f_func := f_func,
		f_domain := f_domain,
		f_range := begin
			ext y,
			rw mem_range_iff f_func,
			split,
			{
				intro h,
				rcases h with ⟨x, x_dom, hxf⟩,
				rw hxf,
				rw← f_domain at hfφ,
				have := (hfφ (f @@ x) x_dom).mp rfl,
				change f @@ x = ord_pair 0 x at this,
				rw [this, mem_prod_pair, mem_sing],
				rw f_domain at x_dom,
				exact ⟨rfl, x_dom⟩,				
			},
			{
				intro h,
				rw mem_prod at h,
				rcases h with ⟨a, b, ha, hb, hab⟩,
				rw mem_sing at ha,
				rw ha at *,
				rw f_domain,
				use [b, hb],
				rw hab,
				exact eq.symm ((hfφ (f @@ b) hb).mp rfl),
			},
		end,
		f_injective := begin 
			rw injective_iff f_func,
			intros x y x_dom y_dom hfxy,
			rw← f_domain at hfφ,

			have hfx := (hfφ (f @@ x) x_dom).mp rfl,
			have hfy := (hfφ (f @@ y) y_dom).mp rfl,

			change f @@ x = ord_pair 0 x at hfx,
			change f @@ y = ord_pair 0 y at hfy,
			
			rw hfx at hfxy,
			rw hfy at hfxy,

			rw ord_pair_eq_iff at hfxy,
			exact hfxy.2,
		end,
		f_isomorphism := begin 
			intros x y x_dom y_dom,

			have hfx := (hfφ (f @@ x) x_dom).mp rfl,
			have hfy := (hfφ (f @@ y) y_dom).mp rfl,

			change f @@ x = ord_pair 0 x at hfx,
			change f @@ y = ord_pair 0 y at hfy,

			rw [hfx, hfy],
			rw dict_pair  has_mem.mem has_mem.mem,
			have temp : ¬((0:Set) ∈ (0:Set)),
			{
				intro h,
				unfold has_zero.zero at h,
				exact not_mem_empty h,
			},
			simp [temp],
		end
	},

	have h_ss : (sing 0 × α) ⊆ ord_sum_set α β,
	{
		intros x hx,
		unfold ord_sum_set,
		rw mem_pair_union,
		exact or.inl hx,
	},

	have h_ord := (type_ord (ord_sum_set α β) (ord_sum_order α β)),
	have h_wo : well_order (ord_sum_set α β) (ord_sum_order α β)
	:= wo_of_ord_sum_set α_ord β_ord,

	have := type_le_of_subset_wo h_wo h_ss,
	unfold ord_sum_order at this,
	rw ←type_unique' f_iso at this,
	unfold has_add.add ord_sum,
	rw type_of_ord α_ord at this,
	exact this,
end

lemma mem_func_of_mem_domain {f x : Set} (f_func : set_function f) (x_dom : x ∈ domain f) :
ord_pair x (f @@ x) ∈ f := func_spec f_func x_dom


lemma ordinal_of_mem_ordinal {α : Set} (α_ord : ordinal α) {b : Set} (h : b ∈ α) : ordinal b :=
ord_of_mem_ON (mem_of_ordinal_is_ordinal (mem_ON_of_ord α_ord) h)

lemma ord_sum_succ {α β : Set} (α_ord : ordinal α) (β_ord : ordinal β) :
α + succ β = succ (α + β) := 
begin 
	have f_iso := (type_iso (wo_of_ord_sum_set α_ord β_ord)),
	set f := type_isomorphism (wo_of_ord_sum_set α_ord β_ord),

	let g := f ∪ sing (ord_pair (ord_pair 1 β) (α + β)),
	have g_func : set_function g,
	{
		fconstructor,
		intros p hp,
		rw mem_pair_union at hp,
		cases hp,
		{
			rcases f_iso.f_func.is_func hp with ⟨b, a, hab⟩,

			have a_dom : a ∈ domain f,
			{
				rw hab.1 at hp,
				rw mem_domain,
				use [b, hp],
			},

			have b_range : b ∈ range f,
			{
				rw hab.1 at hp,
				rw mem_range,
				use [a, hp],
			},


			use [b, a, hab.1],
			intros c hc,
			rw mem_pair_union at hc,
			cases hc,
			{exact hab.2 hc},
			{
				exfalso,
				rw mem_sing at hc,
				rw ord_pair_eq_iff at hc,
				rw f_iso.f_domain at a_dom,
				unfold ord_sum_set at a_dom,
				rw mem_pair_union at a_dom,
				rw hc.1 at *,
				rw [mem_prod_pair, mem_prod_pair, mem_sing, mem_sing] at a_dom,
				cases a_dom,
				{
					exact zero_ne_one (eq.symm a_dom.1),
				},
				{exact ord_not_mem_self (mem_ON_of_ord β_ord) a_dom.2},
			},
		},
		{
			rw mem_sing at hp,
			use [α+β, ord_pair 1 β, hp],
			intros c hc,
			rw mem_pair_union at hc,
			cases hc,
			{
				exfalso,
				have : ord_pair 1 β ∈ domain f,
				{
					rw mem_domain,
					use c,
					exact hc,
				},
				rw f_iso.f_domain at this,
				unfold ord_sum_set at this,
				rw [mem_pair_union, mem_prod_pair] at this,
				cases this,
				{
					rw mem_sing at this,
					exact zero_ne_one (eq.symm this.1),
				},
				{
					rw mem_prod_pair at this,
					exact ord_not_mem_self (mem_ON_of_ord β_ord) this.2,
				},
			},
			{
				rw mem_sing at hc,
				rw ord_pair_eq_iff at hc,
				rw ord_pair_eq_iff at hc,
				exact eq.symm hc.2,
			},
		},
	},

	have g_domain : domain g = domain f ∪ sing (ord_pair 1 β),
	{
		ext x,
		split,
		{
			intro h,
			rw mem_domain at h,
			cases h with b hb,
			rw mem_pair_union at hb,
			rw mem_pair_union,
			cases hb,
			{
				left,
				rw mem_domain,
				use [b, hb],
			},
			{
				right,
				rw mem_sing at *,
				rw ord_pair_eq_iff at hb,
				exact hb.1,
			},
		},
		{
			intro h,
			rw mem_pair_union at h,
			rw mem_domain at h ⊢,
			cases h,
			{
				cases h with b hb,
				use b,
				rw mem_pair_union,
				exact or.inl hb,
			},
			{
				rw mem_sing at h,
				use α + β,
				rw mem_pair_union,
				rw mem_sing,
				rw ord_pair_eq_iff,
				exact or.inr ⟨h, rfl⟩,
			},
		},
	},

	have hfg : ∀⦃x⦄, x ≠ ord_pair 1 β → g @@ x = f @@ x,
	{
		intros x hx,
		by_cases x ∈ domain f,
		{
			have : ord_pair x (f @@ x) ∈ g,
			{
				rw mem_pair_union,
				exact or.inl (mem_func_of_mem_domain f_iso.f_func h),
			},

			exact eq.symm (func_unique g_func this),
		},
		{
			rw func_out (@not_and_of_not_right (is_set_function f) (x ∈ domain f) h),
			have : x ∉ domain g,
			{
				intro h2,
				rw g_domain at h2,
				rw mem_pair_union at h2,
				rw mem_sing at h2,
				have : x = ord_pair 1 β := by tauto,
				exact hx this,
			},
			rw func_out (@not_and_of_not_right (is_set_function g) (x ∈ domain g) this),
		},
	},

	have hfg_2 : ∀⦃x⦄, x ∈ domain f → g @@ x = f @@ x,
	{
		intros x hx,
		have : x ≠ ord_pair 1 β,
		{
			intro x_eq,
			rw f_iso.f_domain at hx,
			unfold ord_sum_set at hx,
			rw mem_pair_union at hx,
			rw x_eq at hx,
			rw mem_prod_pair at hx,
			cases hx,
			{
				rw mem_sing at hx,
				exact zero_ne_one (eq.symm hx.1),
			},
			{
				rw mem_prod_pair at hx,
				exact ord_not_mem_self (mem_ON_of_ord β_ord) hx.2,
			},
		},
			exact hfg this,
	},

	have h_ss : sing ∅ × α ∪ sing 1 × β ⊆ sing ∅ × α ∪ sing 1 × succ β,
	{
		intros p hp,
		rw [mem_pair_union, mem_prod, mem_prod] at hp ⊢,
		cases hp,
		{exact or.inl hp},
		{
			right,
			rcases hp with ⟨a, b, ha, hb, hab⟩,
			use [a, b, ha],
			exact ⟨ord_lt_of_lt_of_lt (succ_of_ordinal_is_ordinal β_ord) hb (lt_succ_self β), hab⟩,
		},
	},

	have hg_oneβ : g @@ (ord_pair 1 β) = α + β,
	{
		have : (ord_pair (ord_pair 1 β) (α + β)) ∈ g,
		{
			rw mem_pair_union,
			rw mem_sing,
			right,
			refl,
		},

		exact eq.symm (func_unique g_func this),
	},

	have g_isomorphism : ∀ ⦃a1 a2 : Set⦄, a1 ∈ ord_sum_set α (succ β) → 
	a2 ∈ ord_sum_set α (succ β) → (ord_sum_order α (succ β) a1 a2 ↔ g @@ a1 ∈ g @@ a2),
	{
			intros p1 p2 hp1 hp2,
			have hp1' := hp1,
			have hp2' := hp2,
			unfold ord_sum_set at hp1 hp2,
			rw [mem_pair_union, mem_prod, mem_prod] at hp1 hp2,
			cases hp1,
			{
				rcases hp1 with ⟨a, b, ha, hb, hab⟩,
				rw mem_sing at ha,
				rw ha at *, clear ha a,
				have p1_ne : p1 ≠ ord_pair 1 β,
				{
					intro p1_eq,
					rw hab at p1_eq,
					rw ord_pair_eq_iff at p1_eq,
					exact zero_ne_one p1_eq.1,
				},

				have hp1_dom : p1 ∈ ord_sum_set α β,
					{
						unfold ord_sum_set,
						rw mem_pair_union,
						left,
						rw hab,
						rw mem_prod_pair,
						rw mem_sing,
						exact ⟨rfl, hb⟩,
					},

				rw hfg p1_ne,

				cases hp2,
				{
					rcases hp2 with ⟨a, c, ha, hc, hac⟩,
					rw mem_sing at ha,
					rw ha at *, clear ha a,

					have p2_ne : p2 ≠ ord_pair 1 β,
					{
						intro p2_eq,
						rw hac at p2_eq,
						rw ord_pair_eq_iff at p2_eq,
						exact zero_ne_one p2_eq.1,
					},

					rw hfg p2_ne,
					have hp2_dom : p2 ∈ ord_sum_set α β,
					{
						unfold ord_sum_set,
						rw mem_pair_union,
						left,
						rw hac,
						rw mem_prod_pair,
						rw mem_sing,
						exact ⟨rfl, hc⟩,
					},
					rw← f_iso.f_isomorphism hp1_dom hp2_dom,
					refl,
				},
				{
					rcases hp2 with ⟨a, c, ha, hc, hac⟩,
					rw mem_sing at ha,
					rw ha at *, clear ha a,
					rw mem_succ at hc,
					cases hc,
					{
						have p2_ne : p2 ≠ ord_pair 1 β,
						{
							intro p2_eq,
							rw hac at p2_eq,
							rw ord_pair_eq_iff at p2_eq,
							rw p2_eq.2 at hc,
							exact ord_not_mem_self (mem_ON_of_ord β_ord) hc,
						},

						rw hfg p2_ne,
						have hp2_dom : p2 ∈ ord_sum_set α β,
						{
							unfold ord_sum_set,
							rw mem_pair_union,
							right,
							rw hac,
							rw mem_prod_pair,
							rw mem_sing,
							exact ⟨rfl, hc⟩,
						},

						rw← f_iso.f_isomorphism hp1_dom hp2_dom,
						refl,

					},
					{
						rw hc at *,
						rw hac,
						rw hg_oneβ,
						unfold has_add.add ord_sum,
						unfold ord_sum_set ord_sum_order at f_iso hp1_dom,
						rw← f_iso.f_range,
						rw← f_iso.f_domain at hp1_dom, 
						have := mem_range_of_mem_dom f_iso.f_func hp1_dom,
						split,
						{exact λh, this},
						{
							intro h,
							unfold ord_sum_order,
							rw hab,
							rw dict_pair,
							left,
							unfold has_one.one,
							exact lt_succ_self ∅,
						},
					},
				},
			},
			{
				rcases hp1 with ⟨a, b, ha, hb, hab⟩,
				rw mem_sing at ha, rw ha at *, clear ha a,
				rw mem_succ at hb,
				cases hb,
				{
					have p1_ne : p1 ≠ ord_pair 1 β,
					{
						intro p1_eq,
						rw p1_eq at hab,
						rw ord_pair_eq_iff at hab,
						rw← hab.2 at hb,
						exact ord_not_mem_self (mem_ON_of_ord β_ord) hb,
					},
					rw hfg p1_ne,
					cases hp2,
					{
						rcases hp2 with ⟨c, d, hc, hd, hcd⟩,
						rw mem_sing at hc, rw hc at *, clear hc c,
						split,
						{
							intro h,
							unfold ord_sum_order at h,
							rw [hab, hcd, dict_pair] at h,
							exfalso,
							cases h,
							{exact not_mem_empty h},
							{exact zero_ne_one (eq.symm h.1)},
						},
						{
							intro h,
							have p2_ne : p2 ≠ ord_pair 1 β,
							{
								intro p2_eq,
								rw p2_eq at hcd,
								rw ord_pair_eq_iff at hcd,
								exact zero_ne_one (eq.symm hcd.1),
							},

							have hp1_dom : p1 ∈ ord_sum_set α β,
							{
								unfold ord_sum_set,
								rw mem_pair_union,
								right,
								rw hab,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hb⟩,
							},


							have hp2_dom : p2 ∈ ord_sum_set α β,
							{
								unfold ord_sum_set,
								rw mem_pair_union,
								left,
								rw hcd,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hd⟩,
							},

							rw hfg p2_ne at h,
							rw← f_iso.f_isomorphism hp1_dom hp2_dom at h,
							unfold ord_sum_order at *,
							exact h,
						},
					},
					{
						rcases hp2 with ⟨c, d, hc, hd, hcd⟩,
						rw mem_sing at hc, rw hc at *, clear hc c,
						unfold ord_sum_order,
						rw mem_succ at hd,
						cases hd,
						{
							have p2_ne : p2 ≠ ord_pair 1 β,
							{
								intro p2_eq,
								rw p2_eq at hcd,
								rw ord_pair_eq_iff at hcd,
								rw← hcd.2 at hd,
								exact ord_not_mem_self (mem_ON_of_ord β_ord) hd,
							},
							have hp1_dom : p1 ∈ ord_sum_set α β,
							{
								unfold ord_sum_set,
								rw mem_pair_union,
								right,
								rw hab,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hb⟩,
							},

							have hp2_dom : p2 ∈ ord_sum_set α β,
							{
								unfold ord_sum_set,
								rw mem_pair_union,
								right,
								rw hcd,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hd⟩,
							},

							rw hfg p2_ne,
							rw← f_iso.f_isomorphism hp1_dom hp2_dom,
							refl,
						},
						{
						have hp1_dom : p1 ∈ ord_sum_set α β,
							{
								unfold ord_sum_set,
								rw mem_pair_union,
								right,
								rw hab,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hb⟩,
							},
							rw hd at hcd,
							rw hcd,
							rw hg_oneβ,
							unfold has_add.add ord_sum,
							unfold ord_sum_set ord_sum_order at f_iso hp1_dom,
							rw← f_iso.f_range,
							rw← f_iso.f_domain at hp1_dom, 
							split,
							{exact λh, mem_range_of_mem_dom f_iso.f_func hp1_dom},
							{
								intro h,
								rw hab,
								rw dict_pair,
								exact or.inr ⟨rfl, hb⟩,
							},
						},
					},
				},
				{
					rw hb at hab,
					rw [hab, hg_oneβ],
					cases hp2,
					{
						rcases hp2 with ⟨c, d, hc, hd, hcd⟩,
						rw mem_sing at hc, rw hc at *, clear hc c,
						have p2_dom : p2 ∈ domain f,
						{
								rw f_iso.f_domain,
								unfold ord_sum_set,
								rw mem_pair_union,
								left,
								rw hcd,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hd⟩,
						},

						rw hfg_2 p2_dom,
						have hfp2 : f @@ p2 ∈ α + β,
						{
							unfold has_add.add ord_sum,
							unfold ord_sum_set ord_sum_order at f_iso,
							rw← f_iso.f_range,
							exact mem_range_of_mem_domain f_iso.f_func p2_dom,
						},

						split,
						{
							intro h2,
							unfold ord_sum_order at h2,
							rw hcd at h2,
							rw dict_pair at h2,
							exfalso,
							cases h2,
							{exact not_mem_empty h2},
							{exact zero_ne_one (eq.symm h2.1)},
						},
						{
							intro h2,
							exfalso,
							exact not_ord_mem_ord (ord_of_ord_sum α β) h2 hfp2,
						},

					},
					{
						rcases hp2 with ⟨c, d, hc, hd, hcd⟩,
						rw mem_sing at hc, rw hc at *, clear hc c,
						rw mem_succ at hd,
						cases hd,
						{
							have hp2_dom : p2 ∈ domain f,
							{
								rw f_iso.f_domain,
								unfold ord_sum_set,
								rw mem_pair_union,
								right,
								rw hcd,
								rw mem_prod_pair,
								rw mem_sing,
								exact ⟨rfl, hd⟩,
							},

							rw hfg_2 hp2_dom,
							split,
							{
								intro h2,
								rw hcd at h2,
								unfold ord_sum_order at h2,
								rw dict_pair at h2,
								exfalso,
								cases h2,
								{exact ord_not_mem_self (mem_ON_of_ord one_ord) h2},
								{
									exact not_ord_mem_ord β_ord h2.2 hd,
								},
							},
							{
								have hfp2 : f @@ p2 ∈ α + β,
								{
									unfold has_add.add ord_sum,
									unfold ord_sum_set ord_sum_order at f_iso,
									rw← f_iso.f_range,
									exact mem_range_of_mem_domain f_iso.f_func hp2_dom,
								},
								intro h2, exfalso,
								exact not_ord_mem_ord (ord_of_ord_sum α β) h2 hfp2,
							},
						},
						{
							rw hd at hcd,
							rw hcd,
							rw hg_oneβ,
							unfold ord_sum_order,
							rw dict_pair,
							split,
							{
								intro h2,
								exfalso,
								cases h2,
								{
									exact ord_not_mem_self (mem_ON_of_ord one_ord) h2,
								},
								{
									exact ord_not_mem_self (mem_ON_of_ord β_ord) h2.2,
								},
							},
							{
								intro h2,
								exfalso,
								exact ord_not_mem_self (mem_ON_of_ord (ord_of_ord_sum α β)) h2,
							},
						},
					},
				},
			},
	},

	have g_domain' : domain g = (ord_sum_set α (succ β)),
	{
			rw g_domain,
			rw f_iso.f_domain,
			unfold ord_sum_set,
			ext p,
			rw [mem_pair_union, mem_pair_union, mem_pair_union] at *,
			split,
			{
				intro h,
				cases h, cases h,
				{exact or.inl h},
				{
					right,
					rw mem_prod at *,
					rcases h with ⟨a, b, ha, hb, hab⟩,
					use [a, b, ha],
					exact 
					⟨ord_lt_of_lt_of_lt (succ_of_ordinal_is_ordinal β_ord) hb (lt_succ_self β), hab⟩,
				},
				{
					rw mem_sing at h,
					right,
					rw mem_prod,
					use [1, β],
					rw mem_sing,
					use [rfl, lt_succ_self β, h],
				},
			},
			{
				intro h,
				cases h,
				{left, left, exact h},
				{
					rw mem_prod at h,
					rcases h with ⟨a, b, ha, hb, hab⟩,
					rw mem_sing at ha ⊢,
					rw ha at hab,
					rw mem_succ at hb,
					cases hb,
					{
						left, right,
						rw mem_prod,
						use [1, b],
						rw mem_sing,
						use [rfl, hb, hab],
					},
					{rw hb at hab, exact or.inr hab},
				},
			},	
	}, 

	have g_range : range g = succ (α + β),
	{
			ext y,
			rw mem_range_iff g_func,
			split,
			{
				intro h,
				rcases h with ⟨x, x_dom, hxy⟩,
				rw hxy,
				rw [g_domain, mem_pair_union] at x_dom,
				cases x_dom,
				{
					rw hfg_2 x_dom,
					rw mem_succ, left,
					unfold has_add.add ord_sum,
					unfold ord_sum_set ord_sum_order at f_iso,
					rw← f_iso.f_range,
					exact mem_range_of_mem_domain f_iso.f_func x_dom,
				},
				{
					rw mem_sing at x_dom,
					have : ord_pair x (α + β) ∈ g,
					{
						rw mem_pair_union,
						rw x_dom,
						rw mem_sing,
						exact or.inr rfl,
					},

					rw func_unique g_func this,
					exact lt_succ_self (g @@ x),
				},
			},
			{
				intros y,
				rw mem_succ at y,
				cases y with h,
				{
					unfold has_add.add ord_sum at h,
					unfold ord_sum_set ord_sum_order at f_iso,
					rw← f_iso.f_range at h,
					rcases mem_range_is_func f_iso.f_func h with ⟨x, x_dom, hxy⟩,
					rw← hxy,
					use x,
					rw g_domain,
					rw mem_pair_union,
					use or.inl x_dom,
					exact eq.symm (hfg_2 x_dom),
				},
				{
					use ord_pair 1 β,
					rw g_domain,
					rw mem_pair_union,
					rw mem_sing,
					use or.inr rfl,
					rw y_1,
					have : ord_pair (ord_pair 1 β) (α+β) ∈ g,
					{
						rw mem_pair_union,
						rw mem_sing,
						exact or.inr rfl,
					},
					exact func_unique g_func this,
				},
			},
	},

	have g_iso : order_isomorphism g (ord_sum_set α (succ β)) 
	(ord_sum_order α (succ β)) (succ (α + β)) (∈) :=
	{
		f_func := g_func,
		f_domain := g_domain',
		f_range := g_range,
		f_injective := begin 
			rw injective_iff g_func,
			intros p1 p2 p1_dom p2_dom hp1p2,

			have p1_dom' := p1_dom,
			have p2_dom' := p2_dom,

			have gp2_ord : ordinal (g @@ p2),
			{
				have : g @@ p2 ∈ range g := mem_range_of_mem_domain g_func p2_dom,
				rw g_range at this,
				exact ordinal_of_mem_ordinal (succ_of_ordinal_is_ordinal (ord_of_ord_sum α β)) this,
			},

			rw g_domain' at p1_dom p2_dom,

			cases (wo_of_ord_sum_set α_ord (succ_of_ordinal_is_ordinal β_ord)).tri p1_dom p2_dom,
			{
				exfalso,
				have := (g_isomorphism p1_dom p2_dom).mp h,
				rw hp1p2 at this,
				exact ord_not_mem_self (mem_ON_of_ord gp2_ord) this,
			},
			{
				cases h,
				{
					exfalso,
					have := (g_isomorphism p2_dom p1_dom).mp h,
					rw hp1p2 at this,
					exact ord_not_mem_self (mem_ON_of_ord gp2_ord) this,
				},
				{exact h}
			},
		end,
		f_isomorphism := g_isomorphism,
	},

	have temp : α + succ β = type (sing ∅ × α ∪ sing 1 × succ β)
	 (dict_order has_mem.mem has_mem.mem) := rfl,
	rw temp,

	exact eq.symm
	 (type_unique (succ_of_ordinal_is_ordinal (ord_of_ord_sum α β)) g_iso),

end

lemma one_plus_one : 1 + 1 = succ 1 :=
begin 
	have := ord_sum_succ one_ord empty_is_ordinal,
	change 1 + succ 0 = succ (1 + 0) at this,
	rw ord_sum_zero one_ord at this,
	exact this,
end

lemma ord_sum_le_of_le_left {α β γ: Set} (α_ord : ordinal α) (β_ord : ordinal β) (γ_ord : ordinal γ) :
β ≤ γ → α + β ≤ α + γ :=
begin
	intro hβγ,
	apply type_le_of_subset_wo (wo_of_ord_sum_set α_ord γ_ord),
	unfold ord_sum_set,

	intros p hp,
	rw mem_pair_union at hp,
	cases hp,
	{
		rw mem_prod at hp,
		rcases hp with ⟨a, b, ha, hb, hp⟩,
		rw mem_sing at ha, rw ha at *, clear ha a,
		rw hp,
		rw mem_pair_union,
		left,
		rw [mem_prod_pair, mem_sing],
		exact ⟨rfl, hb⟩,
	},
	{
		rw mem_prod at hp,
		rcases hp with ⟨a, b, ha, hb, hp⟩,
		rw mem_sing at ha, rw ha at *, clear ha a,
		rw hp,
		rw mem_pair_union,
		right,
		rw [mem_prod_pair, mem_sing],
		exact ⟨rfl, ord_lt_of_lt_of_le γ_ord hb hβγ⟩,
	},
end

lemma omega_induction {φ : fclass} (h_base : φ 0) (h_inductive : ∀⦃n⦄, n ∈ ω → φ n → φ (succ n)) :
∀⦃n⦄, n ∈ ω → φ n :=
begin 
	set ψ := λn, n ∈ ω ∧ φ n with ψ_def,
	have h1 : inductive_class ψ,
	{
		unfold inductive_class,
		split,
		{
			unfold has_mem.mem mem_class,
			rw ψ_def,
			rw mem_omega,
			exact ⟨empty_is_nat, h_base⟩,
		},
		{
			intros y hy,
			unfold has_mem.mem mem_class,
			rw ψ_def at hy ⊢,
			unfold has_mem.mem mem_class at hy,
			split,
			{
				rw mem_omega (succ y),
				have := mem_omega y, unfold has_mem.mem at this,
				rw this at hy,
				exact succ_of_nat_is_nat hy.1,
			},
			{exact h_inductive hy.1 hy.2,},

		},
	},
	have h2 : subclass_set ψ ω := λn h, h.1,
	rcases induction_class h1 h2 with ⟨I, hI⟩,
	rw← hI,
	intros n hn,
	rw mem_set_of at hn,
	exact hn.2,
end

lemma ord_succ_eq_add_one {α : Set} (α_ord : ordinal α) : succ α = α + 1 := 
begin 
	unfold has_one.one,
	rw ord_sum_succ α_ord empty_is_ordinal,
	have := ord_sum_zero α_ord,
	unfold has_zero.zero at this,
	rw this,
end

lemma ord_of_mem_omega {a : Set} (a_nat : a ∈ ω) : ordinal a := ordinal_of_mem_ordinal omega_ord a_nat

lemma add_closed_omega {a b : Set} (a_nat : a ∈ ω) (b_nat : b ∈ ω) : a + b ∈ ω :=
begin
	set φ := λn, a + n ∈ ω with φ_def,
	have h_base : φ 0 :=
	begin 
		rw [φ_def, ord_sum_zero (ord_of_mem_omega a_nat)],
		exact a_nat,
	end,

	have h_inductive : ∀⦃n⦄, n ∈ ω → φ n → φ (succ n) :=
	begin 
		intros n n_nat hn,
		rw φ_def at *,
		rw ord_sum_succ (ord_of_mem_omega a_nat) (ord_of_mem_omega n_nat),
		rw mem_omega at ⊢ hn,
		exact succ_of_nat_is_nat hn,
	end,

	have := (omega_induction h_base h_inductive) b_nat,
	exact this,
end

namespace natural
@[ext]structure natural :=
(set : Set)
(nat : set ∈ ω)

def ord_of_nat (a : natural) : ordinal a.set := ord_of_mem_omega a.nat

instance : has_add natural := 
⟨λa b, ⟨a.set + b.set, add_closed_omega a.nat b.nat⟩⟩

instance : has_zero natural := ⟨⟨0, begin
	rw mem_omega,
	exact empty_is_nat,
end⟩⟩

instance : has_one natural := ⟨⟨1, begin
	rw mem_omega,
	exact succ_of_nat_is_nat (empty_is_nat),
end⟩⟩

lemma eq_of_set_eq {a b : natural} (h : a.set = b.set) : a = b := natural.ext a b h

lemma add_zero (a : natural) : a + 0 = a := 
begin 
	have eq := ord_sum_zero (ord_of_nat a),
	unfold has_add.add at *,
	have : (0:natural).set = 0 := rfl,
	rw← this at eq,
	apply eq_of_set_eq,
	simp,
	exact eq,
end

lemma add_succ (a b : natural) : a + (b + 1) = (a + b) + 1 :=
begin 
	have := ord_succ_eq_add_one (ord_of_ord_sum a.set b.set),
	unfold has_add.add has_one.one at *,
	simp,
	rw← this,
	have := ord_sum_succ (ord_of_nat b) empty_is_ordinal,
	unfold has_add.add at this,
	rw this,
	have := ord_sum_zero (ord_of_nat b),
	unfold has_add.add has_zero.zero at this,
	rw this,
	apply ord_sum_succ,
	{exact ord_of_nat a},
	{exact ord_of_nat b},
end

lemma add_one (a : natural) : a + 1 = ⟨succ a.set, 
begin 
	have := a.nat,
	rw mem_omega at *,
	exact succ_of_nat_is_nat this,
end⟩ := 
begin 
	apply eq_of_set_eq,
	simp,
	rw ord_succ_eq_add_one (ord_of_nat a),
	refl,
end

lemma succ_inj {a b : natural} (h : a + 1 = b + 1) : a = b := 
begin 
	rw [add_one, add_one] at h,
	apply eq_of_set_eq,
	exact succ_inj_on_ON (ord_of_nat a) (natural.mk.inj h),
end

lemma zero_not_succ (a : natural) : a + 1 ≠ 0 :=
begin 
	intro h,
	rw add_one at h,
	have := lt_succ_self a.set,
	rw (natural.mk.inj h) at this,
	exact not_mem_empty this,
end

lemma induction (φ : natural → Prop) (h_base : φ 0) 
(h_inductive : ∀n, φ n → φ (n + 1)) : ∀n, φ n :=
begin 
	set ψ := λn, ∃nat, φ ⟨n, nat⟩ with ψ_def,
	have h1 : ψ 0 :=
	begin 
		rw ψ_def,
		simp,
		use empty_is_nat,
		exact h_base,
	end,

	have h2 : ∀⦃n⦄, n ∈ ω → ψ n → ψ (succ n),
	{
		intros n gbg hn, clear gbg,
		rcases hn with ⟨n_nat, hφ⟩,
		have := h_inductive ⟨n, n_nat⟩ hφ,
		rw ψ_def,
		simp,
		use succ_of_nat_is_nat (by rwa mem_omega at n_nat),
		rw add_one at this,
		exact this,
	},

	intro n,
	cases (omega_induction h1 h2) n.nat with hφ hnat,
	rwa @eq_of_set_eq {set := n.set, nat := hφ} n rfl at hnat,
end

lemma zero_add (a : natural) : 0 + a = a :=
begin 
	set φ := λn : natural, 0 + n = n with φ_def,
	apply (induction φ (add_zero 0) _) a,
	{
		intros n hn,
		rw φ_def at *,
		rw add_succ 0 n,
		rw hn,
	},
end

lemma add_assoc (a b c : natural) : a + (b + c) = (a + b) + c :=
begin 
	set φ := λn : natural, a + (b + n) = (a + b) + n with φ_def,
	apply induction φ _ _,
	{
		rw [φ_def, add_zero, add_zero],
	},
	{
		intros n hn,
		rw φ_def at *,
		rw [add_succ b n, add_succ a (b+n), hn, add_succ (a+b) n],
	}
end

lemma succ_add (a b : natural) : (a + 1) + b = (a + b) + 1 :=
begin 
	set φ := λn : natural, (a + 1) + n = (a + n) + 1 with φ_def,
	apply induction φ _ _,
	{
		rw [φ_def, add_zero, add_zero],
	},
	{
		intros n hn,
		rw φ_def at *,
		rw [add_succ, add_succ, hn],
	},
end

lemma add_comm (a b : natural) : a + b = b + a :=
begin 
	set φ := λn : natural, a + n = n + a with φ_def,
	apply induction φ (by rw [φ_def, add_zero, zero_add]) _,
	{
		intros n hn,
		rw φ_def at *,
		rw [add_succ, succ_add, hn],
	},
end

lemma add_right_cancel (a b c : natural) (h : a + c = b + c) : a = b :=
begin 
	set φ := λn : natural, a + n = b + n → a = b with φ_def,
	have := induction φ _ _,
	swap,
	{
		rw [φ_def, add_zero, add_zero],
		exact λh, h
	},
	swap,
	{
		intros n hn h,
		rw φ_def at *,
		apply hn,
		rw [add_assoc, add_assoc] at h,
		exact succ_inj h,
	},

	exact this c h,
end

end natural

structure injection (f A B : Set) :=
(f_func : set_function f)
(f_domain : domain f = A)
(f_range : range f ⊆ B)
(f_injective : injective f)

infix ` ≼` :50 := λ (A B : Set), ∃(f : Set) (f_inj : injection f A B), true

infix ` ≈ `:50 := λA B, ∃(f : Set) (f_bi : bijection f A B), true

infix ` ≺ `:50 := λ A B, A ≼ B ∧ ¬A ≈ B

lemma cantors_theorem_helper {A f : Set} (f_func : set_function f) (hfA : domain f = A) : 
¬ 𝒫 A ⊆ range f :=
begin 
	intro h,
	let B := {x ∈ A | ∃(hx : x ∈ domain f), x ∉ eval f hx},
	have hB : B ∈ 𝒫 A,
	{
		rw mem_powerset,
		intros y hy,
		rw mem_sep at hy,
		exact hy.1,
	},
	have B_ss := h hB,
	rw mem_range at B_ss,
	rcases B_ss with ⟨x, hxBf⟩,
	have hxf : x ∈ domain f,
	{
		rw mem_domain,
		use [B, hxBf],
	},
	have f_at_x := eval_unique f hxf hxBf,
	have : x ∈ B ↔ x ∉ B,
	{
		clear h,
		split,
		{
			intros h,
			rw mem_sep at h,
			intro contra,
			rcases h with ⟨hxA, hx2, hxf2⟩,
			apply hxf2,
			have := eval_behaves f hxf hx2,
			rw [←this, ←f_at_x],
			exact contra,
		},
		{
			intro h,
			rw mem_sep,
			split,
			{
				rw hfA at hxf,
				exact hxf,
			},
			{
				use hxf,
				rw← f_at_x,
				exact h,
			},
		},
	},
	exact (not_iff_self (x ∈ B)).mp (iff.symm this),
end

theorem cantors_theorem (A : Set) : A ≺ 𝒫 A :=
begin 
	dsimp only,
	split,
	{
		set φ := λx y, y = sing x with φ_def,
		have φ_func : class_function_on_set φ A,
		{
			constructor,
			intros x x_A,
			use [sing x, rfl],

			intros z hz,
			rw φ_def at hz,
			rw hz,
		},
		rcases set_func_of_class_func φ_func with ⟨f, f_func, f_dom, fφ⟩,
		use f,
		have f_inj : injection f A (𝒫 A) := {
			f_func := f_func,
			f_domain := f_dom,
			f_range := begin 
				intros y hy,
				rw mem_range_iff f_func at hy,
				rcases hy with ⟨x, x_dom, hx⟩,
				rw f_dom at x_dom,
				have := (fφ y x_dom).mp (eq.symm hx),
				rw φ_def at this,
				rw this,
				rw mem_powerset,

				intros k hk,
				rw mem_sing at hk,
				rw hk,
				exact x_dom,
			end,
			f_injective := begin 
				rw injective_iff f_func,
				intros x y x_dom y_dom hxy,
				rw← f_dom at fφ,
				rw (fφ (sing x) x_dom).mpr rfl at hxy,
				rw (fφ (sing y) y_dom).mpr rfl at hxy,
				exact (sing_eq x y).mp hxy,
			end,
		},
		use f_inj,
	},
		intro h,
		rcases h with ⟨f, f_bi, -⟩,
		have helper := cantors_theorem_helper f_bi.f_func f_bi.f_domain,
		rw f_bi.f_range at helper,
		exact helper (subset_self 𝒫 A),
end

structure cardinal (κ : Set) extends ordinal κ :=
(is_card : ∀⦃ξ⦄ (ξ_ord : ordinal ξ), ξ ∈ κ → ¬κ ≼ ξ)

def CARD : fclass := λx, ∃(x_card : cardinal x), true

lemma mem_CARD_of_card {κ : Set} (κ_card : cardinal κ) : κ ∈ CARD :=
by use κ_card

lemma card_of_mem_CARD {κ : Set} (κ_card : κ ∈ CARD) : cardinal κ :=
classical.some κ_card

lemma ord_of_card {κ : Set} (κ_card : cardinal κ) : ordinal κ := κ_card.to_ordinal

def eval_on_set (f s : Set) : Set := 
{y ∈ range f | ∃(x : Set) (hxs : x ∈ s), y = f @@ x}

infix ` '' `:500 := eval_on_set

lemma mem_eval_on_set {f s : Set} (f_func : set_function f) (s_dom : s ⊆ domain f) 
(y : Set) : y ∈ f '' s ↔ ∃(x : Set) (hxs : x ∈ s), y = f @@ x 
:=
begin 
	unfold eval_on_set,
	rw mem_sep,
	split,
	{exact λh, h.2},
	{
		intro h,
		rcases h with ⟨x, hxs, hyf⟩,
		rw mem_range_iff f_func,
		exact ⟨⟨x, s_dom hxs, hyf⟩, ⟨x, hxs, hyf⟩⟩,
	}
end

lemma inj_of_subset {A B : Set} (h : A ⊆ B) : A ≼ B :=
begin
	use identity A,
	have f_inj : injection (identity A) A B := {
		f_func := identity_func A,
		f_domain := identity_domain A,
		f_range := 
		begin 
			rw identity_range A,
			exact h,
		end,
		f_injective := identity_injective A,
	},
	use f_inj,
end

lemma ord_isomorphism_of_inj {A : Set} (R : relation) {f : Set} (f_inj : injection f A (range f)) :
order_isomorphism f A R (range f) (λx y, R (f⁻¹ @@ x) (f⁻¹ @@ y)) :=
{
	f_func := f_inj.f_func,
	f_domain := f_inj.f_domain,
	f_range := rfl,
	f_injective := f_inj.f_injective,
	f_isomorphism := begin 
		intros a b a_dom b_dom,
		rw← f_inj.f_domain at a_dom b_dom,
		rw [inv_func f_inj.f_func f_inj.f_injective a_dom, 
		inv_func f_inj.f_func f_inj.f_injective b_dom]
	end
}


lemma card_le_iff {α β: Set} (α_card : cardinal α) (β_card : cardinal β) : α ≤ β ↔ α ≼ β :=
begin
	have α_ord := ord_of_card α_card,
	have β_ord := ord_of_card β_card,
	split,
	{
		rw ord_le_iff_ss α_ord β_ord,
		exact λh, inj_of_subset h
	},
	{
		intro h,
		by_contra gbg,
		have hβα := ord_lt_of_not_le α_ord β_ord gbg, clear gbg,
		exact (α_card.is_card β_ord hβα) h,
	}
end

lemma has_least_ord_of_nonempty_class {φ : fclass} {β : Set} (β_ord : ordinal β) (hβφ : β ∈ φ) : 
∃(α : Set) (α_ord : ordinal α), ∀⦃ξ⦄, ξ ∈ α → ξ ∉ φ :=
begin 
	set X := {α ∈ succ β | φ α} with X_def,
	have sβ_ord := (succ_of_ordinal_is_ordinal β_ord),
	have X_ss : subset_class X ON,
	{
		intros x hx,
		rw mem_sep at hx,
		exact ON_ordinal_class.tran (mem_ON_of_ord sβ_ord) hx.1,
	},
	have X_nonempty : X ≠ ∅,
	{
		intro h,
		have : β ∈ X,
		{
			rw mem_sep,
			exact ⟨lt_succ_self β, hβφ⟩,
		},
		rw h at this,
		exact not_mem_empty this,
	},

	rcases ON_ordinal_class.wo.wf X_ss X_nonempty with ⟨α, αX, α_min⟩,
	have α_ord := ord_of_mem_ON (X_ss αX),
	use [α, α_ord],
	intros ξ ξα hξ,
	have contra : ξ ∈ X,
	{
		rw mem_sep at ⊢ αX,
		exact ⟨sβ_ord.tran αX.1 ξα, hξ⟩,
	},

	exact α_min contra ξα,
end

lemma func_replacement (X : Set) (f : Set → Set) : ∃Y : Set, (∀y, y ∈ Y ↔ ∃x ∈ X, f x = y) :=
begin 
	set φ := λ x y, y = f x with φ_def,
	have φ_func : class_function φ := {
		is_func := 
		begin 
			intros x,
			use f x,
			rw φ_def,
			simp,
		end
	},

	cases @replacement' φ φ_func X with Y hY,
	use Y,
	rw φ_def at hY,
	simp at hY,
	intros y,
	rw← hY y,
	simp,
	split,
	{
		intro h,
		cases h with z hz,
		use z,
		finish,
	},
	{
		intro h,
		cases h with z hz,
		use z,
		finish,
	}
end


theorem hartogs_theorem (A : Set) : ∃(κ : Set) (κ_card : cardinal κ), ¬κ ≼ A :=
begin 
	set W := {p ∈ 𝒫 A × 𝒫 (A × A) | ∃(B R : Set) (hp : p = ord_pair B R)
	 (R_wo : well_order B (λx y, ord_pair x y ∈ R)), true } with W_def,

	set φ := λ(x y : Set), ∃(X R: Set) (hx : x = ord_pair X R) 
	(R_wo : well_order X (λa b, ord_pair a b ∈ R)), y = type X (λa b, ord_pair a b ∈ R) with φ_def,

	have φ_func : class_function_on_set φ W :=
	{
		is_func := 
		begin 
			intros p hp,
			rw [W_def, mem_sep, mem_prod] at hp,
			cases hp with hp hp2,
			rcases hp with ⟨X, R, hX, hR, hp⟩,
			rw hp at *,
			rw mem_powerset at hX hR,
			rcases hp2 with ⟨X', R', hp2, hp3⟩,
			rw ord_pair_eq_iff at hp2,
			rw← hp2.1 at *,
			rw← hp2.2 at *,
			clear hp2,
			rcases hp3 with ⟨R_wo, -⟩,
			use type X (λa b, ord_pair a b ∈ R),
			split,
			{use [X, R, rfl, R_wo]},
			{
				intros z hz,
				rw φ_def at hz,
				rcases hz with ⟨X', R', hx2, R'_wo, hz⟩,
				rw ord_pair_eq_iff at hx2,
				rw← hx2.1 at *,
				rw← hx2.2 at *,
				rw hz,
			}
		end
	},
	have hφ : ∀⦃X R y : Set⦄ (hXR : ord_pair X R ∈ W),
	 φ (ord_pair X R) y ↔ y = type X (λa b, ord_pair a b ∈ R),
	{
		intros X R y hXR,
		split,
		{
			intro h,
			rw φ_def at h,
			rcases h with ⟨X1, R1, hXR1, R1_wo, hy⟩,
			rw ord_pair_eq_iff at hXR1,
			rw [hy, hXR1.1, hXR1.2],
		},
		{
			intro h,
			rw φ_def,
			use [X, R, rfl],
			rw [mem_sep] at hXR,
			rcases hXR.2 with ⟨X1, R1, hXR1, R1_wo, -⟩,
			rw ord_pair_eq_iff at hXR1,
			rw [←hXR1.1, ←hXR1.2] at R1_wo,
			use R1_wo,
			exact h,
		},
	},
	
	rcases restricted_replacement φ_func with ⟨α, hα⟩,
	have α_ss_ON : subset_class α ON,
	{
		intros β hβ,
		rw hα β at hβ,
		rcases hβ with ⟨p, hpW, hp⟩,
		rw φ_def at hp,
		rcases hp with ⟨X, R, hp, hR, hβ⟩,
		rw hβ,
		have := type_ord X (λ (a b : Set), ord_pair a b ∈ R),
		exact mem_ON_of_ord this,
	},
	rcases func_replacement α succ with ⟨β, hβ⟩,
	have β_ss_ON : subset_class β ON,
	{sorry},
	set κ := union β with κ_def,
	use κ,
	have κ_ord := union_ordinal β_ss_ON,
	rw← κ_def at κ_ord,
	have hA : ∀(ξ : Set) (ξ_ord : ordinal ξ) (hξ : ξ ≼ A), ξ < κ,
	{
		intros ξ ξ_ord hξ,
		rcases hξ with ⟨f, hf, -⟩,
		have hf' : injection f ξ (range f) := sorry,
		have f_iso := ord_isomorphism_of_inj (∈) hf',
		set X := range f with X_def,
		set R := λ (x y : Set), f⁻¹ @@ x ∈ f⁻¹ @@ y with R_def,
		have X_wo := wo_of_order_isomorphic_to_wo ξ_ord.wo (inverse_order_isomorphism f_iso),
		have X_ss_A : X ⊆ A,
		{
			rw X_def,
			exact hf.f_range,
		},

		set R_set := {p ∈ A × A | ∃(a b : Set) (hp : p = ord_pair a b), R a b} with R_def',
		have hXR : ord_pair X R_set ∈ W,
		{
			rw [W_def, mem_sep, mem_prod_pair, mem_powerset, mem_powerset],
			split,
			{
				use X_ss_A,
				intros p hp,
				rw [R_def', mem_sep] at hp,
				exact hp.1,
			},
			{
				use [X, R_set, rfl],
				have hR : ∀{a b : Set} (ha : a ∈ A) (hb : b ∈ A), ord_pair a b ∈ R_set ↔R a b, 
				{
					intros a b ha hb,
					rw [R_def, R_def', mem_sep, mem_prod_pair],
					simp,
					split,
					{
						intro h,
						rcases h.2 with ⟨a2, b2, hab2, habR⟩,
						rw ord_pair_eq_iff at hab2,
						rw R_def at habR,
						rw [hab2.1, hab2.2] at *,
						exact habR,
					},
					{
						intro h,
						use [⟨ha, hb⟩, a, b, rfl],
						rw R_def,
						exact h,
					},
				},
				have R_wo : well_order X (λ (x y : Set), ord_pair x y ∈ R_set),
				{
					fconstructor,
					{
						intros x hx,
						have hxA := X_ss_A hx,
						dsimp only,
						rw hR hxA hxA,
						exact X_wo.irrfl hx,
					},
					{
						intros a b c ha hb hc hab hbc,
						rw hR (X_ss_A ha) (X_ss_A hb) at hab,
						rw hR (X_ss_A hb) (X_ss_A hc) at hbc,
						rw hR (X_ss_A ha) (X_ss_A hc) at ⊢,
						exact X_wo.tran ha hb hc hab hbc,
					},
					{
						intros a b ha hb,
						dsimp only,
						rw hR (X_ss_A ha) (X_ss_A hb),
						rw hR (X_ss_A hb) (X_ss_A ha),
						exact X_wo.tri ha hb,
					},
					{
						intros Y Y_ss Y_ne,
						have Y_ss_A := subset_trans Y_ss X_ss_A,
						rcases X_wo.wf Y_ss Y_ne with ⟨y, hyY, hy⟩,
						use [y, hyY],
						intros x hxY,
						dsimp only,
						rw hR (Y_ss_A hxY) (Y_ss_A hyY),
						exact hy hxY,
					},
				},
				use R_wo,
			},
		},

		have XR_α : type X R ∈ α := sorry,
		have XR_β : succ (type X R) ∈ β := sorry,
		have XR_κ : type X R ∈ κ,
		{
			rw κ_def,
			rw mem_union,
			use [succ (type X R), XR_β, lt_succ_self (type X R)],
		},

		have := order_isomorphism_comp f_iso (type_iso X_wo),
		rw (ordinals_isomorphic_iff_eq ξ_ord (type_ord X R)).mp
		 ⟨type_isomorphism X_wo ∘ f, this, trivial⟩,
		 exact XR_κ,

	},
	have κ_card : cardinal κ :=
	{
		wo := κ_ord.wo,
		tran := κ_ord.tran,
		is_card := 
		begin 
			intros ξ ξ_ord hξ,
			sorry
		end,
	},

	sorry,
end

def wf_relation (s y : Set) :=
(∃(s_func : set_function s),
(∃(α : Set) (α_ord : ordinal α), domain s = succ α ∧ y = 𝒫 (s @@ α)) ∨ 
(∃(γ : Set) (γ_ord : ordinal γ) (γ_lim : is_limit γ_ord), 
domain s = γ ∧ y = union (s '' γ))) ∨
((domain s ∉ ON ∨ domain s = ∅ ∨ ¬(∃(s_func : set_function s), true)) ∧ y = ∅)

lemma func_of_wf_relation : class_function wf_relation :=
begin 
	fconstructor,
	unfold is_class_function,
	intros s,
	by_cases ∃(s_func : set_function s)(dom_ord : ordinal (domain s)), domain s ≠ ∅,
	{
		rcases h with ⟨s_func, dom_ord, dom_nonempty⟩,
		by_cases h_lim : is_limit dom_ord,
		{
			use union (s '' (domain s)),
			split,
			{
				left,
				use s_func,
				right,
				use [domain s, dom_ord, h_lim, rfl],
			},
			{
				intros z hz,
				cases hz,
				{
					rcases hz with ⟨-, α, α_ord⟩,
					{
						exfalso,
						rcases α_ord with ⟨α_ord, hsα, hpow⟩,
						exact h_lim.2 ⟨α, α_ord, hsα⟩,
					},
					{
						rcases hz_h with ⟨γ, γ_ord, γ_lim, hdom⟩,
						rw hdom.1,
						exact eq.symm hdom.2,
					},
				},
				cases hz with contra zempty,
				exfalso,
				cases contra,
				{exact contra (mem_ON_of_ord dom_ord)},
				cases contra,
				{exact dom_nonempty contra},
				{exact contra ⟨s_func, trivial⟩}
			},
		},
		{
			unfold is_limit at h_lim,
			push_neg at h_lim,
			specialize h_lim dom_nonempty,
			rcases h_lim with ⟨α, α_ord, hα⟩,
			use 𝒫 (s @@ α),
			split,
			{
				left,
				use [s_func, α, α_ord, hα],
			},
			{
				intros z hz,
				cases hz,
				{
					rcases hz with ⟨-, β, β_ord, hβ⟩,
					rw hα at hβ,
					rw succ_inj_on_ON α_ord hβ.1,
					exact eq.symm hβ.2,

					rcases hz_h with ⟨γ, γ_ord, γ_lim, hγ⟩,
					exfalso,
					rw hα at hγ,
					exact γ_lim.2 ⟨α, α_ord, eq.symm hγ.1⟩,
				},
				{
					exfalso,
					cases hz.1,
					{
						apply h,
						rw hα,
						exact mem_ON_of_ord (succ_of_ordinal_is_ordinal α_ord),
					},
					cases h,
					{exact dom_nonempty h},
					{
						exact h ⟨s_func, trivial⟩,
					},
				},
			},
		},
	},
	{
		push_neg at h,
		use ∅,
		split,
		{
			right,
			split,
			{
				by_contra hcontra,
				push_neg at hcontra,
				have s_ord := ord_of_mem_ON hcontra.1,
				cases hcontra.2.2,
				exact hcontra.2.1 (h w s_ord),
			},
			{refl}
		},
		{
			intros z hz,
			cases hz,
			{
				rcases hz with ⟨s_func, h2⟩,
				cases h2,
				{
					rcases h2 with ⟨α, α_ord, hα⟩,
					have dom_ord : ordinal (domain s),
					{
						rw hα.1,
						exact succ_of_ordinal_is_ordinal α_ord,
					},
					rw h s_func dom_ord at hα,
					exfalso,
					have := lt_succ_self α,
					rw← hα.1 at this,
					exact not_mem_empty this,
				},
				{
					exfalso,
					rcases h2 with ⟨γ, γ_ord, γ_lim, hγ⟩,
					rw← hγ.1 at γ_ord,
					rw h s_func γ_ord at hγ,
					exact γ_lim.1 (eq.symm hγ.1),
				},
			},
			{exact eq.symm hz.2},
		},
	},
end


end test