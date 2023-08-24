package main

type queue struct {
	items []int
}

func (q *queue) Enqueue(i int) {
	q.items = append(q.items, i)
}

func (q *queue) Dequeue() int {
	toRemove := q.items[0]
	q.items = q.items[1:]
	return toRemove
}

func (q *queue) find(i int) bool {
	for _, v := range q.items {
		if v == i {
			return true
		}
	}
	return false
}

func (q *queue) isEmpty() bool {
	return len(q.items) == 0
}
