trait ValueBase {}

struct Value {
    attributes: HashMap<Value, Value>,
    inner: Box<dyn ValueBase>,
}

impl Value {
    fn get_type(&self) -> &'static str {
        self.inner.get_type()
    }
}
