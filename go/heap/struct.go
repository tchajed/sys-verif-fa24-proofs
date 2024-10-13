package heap

type Person struct {
	FirstName string
	LastName  string
	Age       uint64
}

func (p Person) Name() string {
	return p.FirstName + " " + p.LastName
}

func (p *Person) Older(delta uint64) {
	p.Age += delta
}

func (p *Person) GetAge() *uint64 {
	return &p.Age
}

func ExamplePerson() Person {
	return Person{
		FirstName: "Ada",
		LastName:  "Lovelace",
		Age:       25,
	}
}

func ExamplePersonRef() *Person {
	return &Person{
		FirstName: "Ada",
		LastName:  "Lovelace",
		Age:       25,
	}
}

func (p Person) BuggySetAge() {
	p.Age += 1
}

type Rect struct {
	Width  uint64
	Height uint64
}

func (r Rect) Area() uint64 {
	return r.Width * r.Height
}

func (r Rect) IsSquare() bool {
	return r.Width == r.Height
}

func (r *Rect) MakeSquare() {
	r.Height = r.Width
}
