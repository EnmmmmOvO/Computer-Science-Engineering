package main

import (
	"fmt"
	"math/rand"
	"sync"
	"time"
)

type request struct {
	sendId  int
	content int
}

type token struct {
	LN []int
	Q  queue
}

type process struct {
	id          int
	request     bool
	token       *token
	RN          []int
	requestChan []chan request
	tokenChan   []chan *token
	mu          sync.Mutex
}

func (p *process) Send() {
	for {
		// Randomly sleep for a while to simulate the process delay
		time.Sleep(time.Duration(rand.Intn(100)) * time.Millisecond)
		p.mu.Lock()
		p.request = true
		if p.token == nil {
			p.RN[p.id]++
			for i := range p.requestChan {
				if i != p.id {
					// Simulation of network uncertainty in a distributed scenario,
					// 1/50 probability of message loss
					if rand.Intn(50) != 0 {
						// Randomly sleep for a while to simulate the network delay
						time.Sleep(time.Duration(rand.Intn(100)) * time.Millisecond)
						p.requestChan[i] <- request{p.id, p.RN[p.id]}
					} else {
						fmt.Println("Process", p.id, "Requests Message loss")
					}
				}
			}
			p.token = <-p.tokenChan[p.id]
			fmt.Println("Process", p.id, "model1Receive token")
		}
		p.mu.Unlock()

		fmt.Println("Process", p.id, "enter CS")

		p.mu.Lock()
		p.token.LN[p.id] = p.RN[p.id]
		for i := range p.token.LN {
			if i != p.id && !p.token.Q.find(i) && p.RN[i] == p.token.LN[i]+1 {
				p.token.Q.Enqueue(i)
			}
		}

		if !p.token.Q.isEmpty() {
			sendId := p.token.Q.Dequeue()
			p.tokenChan[sendId] <- p.token
			p.token = nil
			fmt.Println("Send Process", p.id, "model1_send token to", sendId)
		}

		p.request = false
		p.mu.Unlock()
	}
}

func (p *process) Receive() {
	receiveChan := p.requestChan[p.id]
	for {
		p.mu.Lock()
		for len(receiveChan) > 0 {
			m := <-receiveChan

			if p.RN[m.sendId] < m.content {
				p.RN[m.sendId] = m.content
			}

			if p.token != nil && !p.request && p.RN[m.sendId] == p.token.LN[m.sendId]+1 {
				p.tokenChan[m.sendId] <- p.token
				p.token = nil
				fmt.Println("Receive Process", p.id, "model1_send token to", m.sendId)
			}
		}
		p.mu.Unlock()
	}
}

func main() {
	const number = 10
	systemToken := new(token)
	systemToken.LN = make([]int, number)
	systemToken.Q = queue{}

	processes := make([]*process, number)
	requestChan := make([]chan request, number)
	tokenChan := make([]chan *token, number)

	for i := 0; i < number; i++ {
		// Accept Request Channel: As not block no matter how many
		// requests the port accepts, set asynchronous channel and
		//give them ample cache space.
		requestChan[i] = make(chan request, 1000)
		// The algorithm set the token is not loss, set it as a
		// synchronous channel to ensure certain acquisitions.
		tokenChan[i] = make(chan *token)
		systemToken.LN[i] = -1
	}

	for i := 0; i < number; i++ {
		processes[i] = &process{
			id:          i,
			request:     false,
			token:       nil,
			RN:          make([]int, number),
			requestChan: requestChan,
			tokenChan:   tokenChan,
		}
		for j := range processes[i].RN {
			processes[i].RN[j] = -1
		}
	}

	// Randomly set the token at any node
	processes[rand.Intn(number)].token = systemToken

	for i := 0; i < number; i++ {
		go processes[i].Receive()
		go processes[i].Send()
	}

	select {}
}
